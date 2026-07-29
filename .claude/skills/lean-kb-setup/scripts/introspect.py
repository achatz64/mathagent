#!/usr/bin/env python3
"""Introspection helpers for the lean-kb-setup skill.

These live in Python rather than the shell for two reasons. The things they
inspect — TOML require blocks, Lake's resolved manifest, HuggingFace snapshot
revisions, Loogle's hashed cache paths — are not safely parseable with grep.
And doing the work here keeps untrusted values (project paths, revisions read
out of files) out of shell word-splitting and heredoc interpolation entirely.

Every subcommand prints JSON on stdout. Exit codes:

    0  the thing was found (see `loogle-index` for the one exception)
    1  the thing is absent
    2  `require` only: the lakefile exists but does not parse

`loogle-index` is deliberately different: it answers "where would the index
be", which has an answer whether or not the file exists, so it always exits 0
and reports presence in its "exists" field. Callers must read that field —
treating its exit status as existence reports every missing index as present.
"""

import argparse
import hashlib
import json
import os
import pathlib
import re
import sys

COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")


class LakefileError(Exception):
    """The lakefile exists but could not be parsed."""


def _strip_comment(line):
    """Drop an inline # comment without cutting inside a quoted string."""
    out, quote = [], None
    for ch in line:
        if quote:
            out.append(ch)
            if ch == quote:
                quote = None
        elif ch in "\"'":
            quote = ch
            out.append(ch)
        elif ch == "#":
            break
        else:
            out.append(ch)
    return "".join(out).strip()


def _unquote(value):
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
        return value[1:-1]
    return value


def load_toml(path):
    """Parse a lakefile. tomllib is 3.11+, so fall back to a block scanner.

    Raises LakefileError rather than returning empty on a parse failure: a
    malformed lakefile silently reported as "no such require" would make the
    caller append a duplicate require block.
    """
    text = path.read_text(encoding="utf-8")
    try:
        import tomllib
    except ImportError:
        tomllib = None

    if tomllib is not None:
        try:
            return tomllib.loads(text)
        except Exception as exc:
            raise LakefileError(f"{path}: {exc}") from exc

    # Python 3.10 fallback: collect [[require]] tables, which is all we need.
    requires, current = [], None
    for raw in text.splitlines():
        line = _strip_comment(raw)
        if not line:
            continue
        if line.startswith("[[require]]"):
            current = {}
            requires.append(current)
        elif line.startswith("["):
            current = None
        elif current is not None and "=" in line:
            key, _, value = line.partition("=")
            current[key.strip()] = _unquote(value)
    return {"require": requires}


def cmd_require(args):
    """What the lakefile *asks* for.

    Classifies the revision syntactically only. Deciding whether a name is a
    reproducible tag or a moving branch needs the remote, so that judgement is
    left to the caller — a blacklist of branch names here would accept
    `develop`, `stable`, or `release-next` as pins.
    """
    path = pathlib.Path(args.project) / "lakefile.toml"
    if not path.exists():
        print(json.dumps({"error": "no lakefile.toml"}))
        return 1
    try:
        parsed = load_toml(path)
    except LakefileError as exc:
        print(json.dumps({"error": str(exc)}))
        return 2

    for req in parsed.get("require", []):
        if req.get("name") == args.name:
            rev = req.get("rev")
            print(
                json.dumps(
                    {
                        "name": args.name,
                        "rev": rev,
                        "git": req.get("git"),
                        "scope": req.get("scope"),
                        # commit | name | none — never a reproducibility verdict.
                        "rev_kind": (
                            "commit" if rev and COMMIT_RE.match(rev)
                            else "name" if rev
                            else "none"
                        ),
                    }
                )
            )
            return 0
    return 1


def cmd_resolved(args):
    """What Lake actually resolved — the commit SHA. This is the real lock."""
    path = pathlib.Path(args.project) / "lake-manifest.json"
    if not path.exists():
        return 1
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except ValueError:
        return 1
    for pkg in data.get("packages", []):
        if pkg.get("name") == args.name:
            print(
                json.dumps(
                    {
                        "name": args.name,
                        "rev": pkg.get("rev"),
                        "inputRev": pkg.get("inputRev"),
                        "url": pkg.get("url"),
                    }
                )
            )
            return 0
    return 1


# The loogle checkout lean-lsp-mcp 0.29.0 builds from, and the layout it keys
# its artefacts on. Mirrored here because install.sh drives the clone/build/index
# itself: routing that work through the `lean_loogle` tool puts it behind
# upstream's fixed 900s build and 300s index timeouts, which a cold Mathlib
# index frequently does not fit inside. Extending the MCP client's own
# wait does nothing about them — they are enforced server-side.
#
# Keep in step with lean_lsp_mcp/loogle.py: REPO_URL, REPO_REF, repo_dir,
# index_path. A drift here builds a second copy beside the one the server looks
# for, and the server would then rebuild it from scratch at first query.
LOOGLE_REPO_URL = "https://github.com/nomeata/loogle.git"
LOOGLE_REPO_REF = "9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0"

# How many measurement attempt records the manifest keeps. A deliberate policy
# limit on file size, not an estimate of anything: records are appended and the
# oldest are dropped whole, never rewritten or summarised.
MAX_ATTEMPT_RECORDS = 100


def _loogle_cache_dir(explicit):
    """Upstream's get_cache_dir(), including the XDG override it honours."""
    if explicit:
        return pathlib.Path(explicit)
    if os.environ.get("LEAN_LOOGLE_CACHE_DIR"):
        return pathlib.Path(os.environ["LEAN_LOOGLE_CACHE_DIR"])
    xdg = os.environ.get("XDG_CACHE_HOME") or (pathlib.Path.home() / ".cache")
    return pathlib.Path(xdg) / "lean-lsp-mcp" / "loogle"


def cmd_loogle_index(args):
    """Every path lean-lsp-mcp uses for this project's local Loogle.

    The index is keyed on sha256 of the *resolved project path* and the repo
    checkout on sha256 of the *toolchain string*, so a glob over the cache can
    pick up a different project's artefacts. Reproduce both keys instead.

    Always exits 0: computing a path is not the same question as whether the
    file is there, and conflating them made a missing index abort the caller
    under `set -e` before it could build one. Read "exists" for that.
    """
    project = pathlib.Path(args.project).resolve(strict=False)
    cache = _loogle_cache_dir(args.cache_dir)

    idx = cache / "index" / (
        "mathlib-%s.idx" % hashlib.sha256(str(project).encode()).hexdigest()[:12]
    )

    # The toolchain string is read raw and stripped, exactly as upstream does.
    # A CRLF checkout would otherwise key the repo directory differently from
    # the one the server goes on to use.
    try:
        toolchain = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError:
        toolchain = None
    repo = cache / ("repo-%s-%s" % (
        LOOGLE_REPO_REF[:12],
        hashlib.sha256((toolchain or "unknown").encode()).hexdigest()[:12],
    ))
    binary = repo / ".lake" / "build" / "bin" / "loogle"

    print(
        json.dumps(
            {
                "path": str(idx),
                "exists": idx.exists(),
                "size": idx.stat().st_size if idx.exists() else 0,
                "cache_dir": str(cache),
                "index_dir": str(cache / "index"),
                "toolchain": toolchain,
                "repo_url": LOOGLE_REPO_URL,
                "repo_ref": LOOGLE_REPO_REF,
                "repo_dir": str(repo),
                "repo_cloned": (repo / ".git").is_dir(),
                "binary": str(binary),
                "binary_exists": binary.is_file(),
            }
        )
    )
    return 0


def _hf_cache_root():
    """Honour the documented HuggingFace cache overrides, in priority order."""
    for var in ("HF_HUB_CACHE", "HUGGINGFACE_HUB_CACHE"):
        if os.environ.get(var):
            return pathlib.Path(os.environ[var])
    if os.environ.get("HF_HOME"):
        return pathlib.Path(os.environ["HF_HOME"]) / "hub"
    return pathlib.Path.home() / ".cache/huggingface/hub"


def cmd_hf_revision(args):
    """The commit `main` points at for a cached model.

    Snapshot directory names are commit hashes, so picking the lexical maximum
    is meaningless — it has no relation to what `main` references or to what
    was actually loaded. Read refs/main instead, and only fall back to a lone
    snapshot when there is exactly one and therefore no ambiguity.
    """
    org, _, name = args.model.partition("/")
    root = _hf_cache_root() / f"models--{org}--{name}"

    ref = root / "refs" / "main"
    if ref.is_file():
        rev = ref.read_text(encoding="utf-8").strip()
        if rev:
            print(json.dumps({"model": args.model, "revision": rev, "source": "refs/main"}))
            return 0

    snaps = sorted(p.name for p in (root / "snapshots").iterdir()) if (root / "snapshots").is_dir() else []
    if len(snaps) == 1:
        print(json.dumps({"model": args.model, "revision": snaps[0], "source": "sole-snapshot"}))
        return 0
    return 1


def _mcp_config_path(scope, repo_root):
    home = pathlib.Path.home()
    if scope == "project":
        return pathlib.Path(repo_root).resolve(strict=False) / ".mcp.json"
    return home / ".claude.json"


def _mcp_child(holder, key, create, label):
    """One level into an MCP config: the child object, or None when absent.

    Membership, never `.get()`. A key that is present and `null` is not a key
    that is missing, and `.get()` cannot tell them apart — which would put a
    JSON null straight back into the "absent" bucket that everything below is
    written to keep it out of. So a present-but-not-an-object value raises,
    `null` included, and only a genuinely missing key may be created.
    """
    if key not in holder:
        if not create:
            return None
        holder[key] = {}
        return holder[key]
    value = holder[key]
    if not isinstance(value, dict):
        raise ValueError("%s is %s, not a JSON object" % (label, json.dumps(value)))
    return value


def _mcp_servers(data, scope, repo_root, create=False):
    """The dict holding mcpServers for one scope, or None when it is absent.

    `local` scope nests under projects.<repo root>, so the three scopes are not
    interchangeable even when two of them share a file.

    Raises ValueError when any container along the way is present but is not an
    object. "Not there" and "there, but not something I understand" are
    different answers, and collapsing the second into the first is the dangerous
    direction: it reports a config we cannot parse as a confident "nothing is
    registered", the caller registers over it, and the snapshot it took to undo
    that says the same thing.
    """
    holder = data
    if scope == "local":
        projects = _mcp_child(data, "projects", create, "projects")
        if projects is None:
            return None
        key = str(pathlib.Path(repo_root).resolve(strict=False))
        holder = _mcp_child(projects, key, create, "projects[%s]" % json.dumps(key))
        if holder is None:
            return None
    return _mcp_child(holder, "mcpServers", create, "mcpServers")


def _looks_empty(value):
    """True when a document holds no information beyond empty containers."""
    if isinstance(value, dict):
        return all(_looks_empty(v) for v in value.values())
    if isinstance(value, list):
        return all(_looks_empty(v) for v in value)
    return value is None


def cmd_mcp_entry(args):
    """Snapshot and restore ONE registration, not the whole config file.

    Whole-file rollback has two failure modes this avoids. It cannot undo a
    registration in `~/.claude.json` without also reverting whatever else
    Claude Code wrote there since the snapshot, so the file was left alone —
    which left a failed `add`'s registration live. And restoring a whole file
    clobbers concurrent unrelated edits.

    Operating on `mcpServers.<name>` at one scope undoes exactly what this skill
    did. The read-modify-write window shrinks from "snapshot until failure" to
    a few milliseconds inside one process.
    """
    path = _mcp_config_path(args.scope, args.repo_root)
    out = {"name": args.name, "scope": args.scope, "source": str(path)}

    if args.action == "get":
        out.update(file_existed=path.is_file(), present=False, entry=None, readable=True)
        try:
            if path.is_file():
                data = json.loads(path.read_text(encoding="utf-8"))
                if not isinstance(data, dict):
                    raise ValueError("config root is not a JSON object")
                servers = _mcp_servers(data, args.scope, args.repo_root) or {}
                if args.name in servers:
                    out["present"] = True
                    out["entry"] = servers[args.name]
        except (OSError, ValueError, TypeError, AttributeError) as exc:
            out.update(readable=False, error=str(exc))
        print(json.dumps(out))
        return 0

    # restore
    try:
        state = json.loads(pathlib.Path(args.state_file).read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(json.dumps({**out, "restored": False, "error": str(exc)}))
        return 1

    if not state.get("readable", True):
        # We never established a before-state, so we cannot undo anything
        # without risking the destruction of something we did not record.
        print(json.dumps({**out, "restored": False, "error": "no readable snapshot"}))
        return 1

    try:
        data = {}
        if path.is_file():
            data = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(data, dict):
                # Starting from {} here would write our entry over whatever the
                # file actually held. Refusing leaves the mess intact and visible.
                raise ValueError("config root is not a JSON object")

        servers = _mcp_servers(data, args.scope, args.repo_root, create=state.get("present", False))
        if state.get("present"):
            servers[args.name] = state.get("entry")
            action = "reinstated"
        else:
            if servers is not None:
                servers.pop(args.name, None)
            action = "removed"

        # The file itself is ours to delete only if it did not exist before and
        # nothing but the entry we removed was ever in it.
        if not state.get("file_existed") and not state.get("present") and _looks_empty(data):
            if path.exists():
                path.unlink()
            print(json.dumps({**out, "restored": True, "action": "removed-file"}))
            return 0

        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({**out, "restored": True, "action": action}))
        return 0
    except (OSError, ValueError, TypeError, AttributeError) as exc:
        print(json.dumps({**out, "restored": False, "error": str(exc)}))
        return 1


def _settings_path(repo_root, settings_file):
    """Which settings file carries the client-side env for this project.

    `settings.local.json` rather than `settings.json`: the value this writes is
    a property of *this host* (how long its page cache lets a Mathlib import
    take), not of the project, and settings.json is the committed one. Writing a
    machine-specific timeout into a shared file would export one box's
    behaviour to every checkout.
    """
    if settings_file:
        return pathlib.Path(settings_file)
    return pathlib.Path(repo_root).resolve(strict=False) / ".claude" / "settings.local.json"


def cmd_settings_env(args):
    """Read, set and roll back ONE key of `env` in a Claude settings file.

    Same discipline as `mcp-entry`, for the same reasons: a config that cannot
    be parsed is *unknown*, never empty, and the whole file is never rewritten
    from scratch. Claude Code owns other keys here (`permissions`,
    `enabledMcpjsonServers`), and clobbering them to set a timeout would be a
    far worse bug than the one being fixed.

    Note that `env` does not appear in the settings key table inside the
    2.1.220 binary, yet it is honoured — verified by experiment on 2026-07-29,
    dropping the page cache to force the failure and observing the timeout take
    effect. Do not "correct" this back to an env-var-only approach on the
    strength of that string table.
    """
    path = _settings_path(args.repo_root, args.settings_file)
    out = {"key": args.key, "source": str(path)}

    def read():
        """(data, error). A missing file is {}; an unparseable one is an error."""
        if not path.is_file():
            return {}, None
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            return None, str(exc)
        if not isinstance(data, dict):
            return None, "settings root is not a JSON object"
        env = data.get("env")
        if "env" in data and not isinstance(env, dict):
            return None, "env is %s, not a JSON object" % json.dumps(env)
        return data, None

    if args.action == "get":
        data, error = read()
        out.update(file_existed=path.is_file(), readable=error is None,
                   present=False, value=None)
        if error is not None:
            out["error"] = error
        else:
            env = data.get("env") or {}
            if args.key in env:
                out.update(present=True, value=env[args.key])
        print(json.dumps(out))
        return 0

    if args.action == "set":
        data, error = read()
        if error is not None:
            # Refuse rather than start from {}: writing our key over a file we
            # could not parse destroys whatever Claude Code had put there, and
            # the snapshot taken to undo it would say the same thing.
            print(json.dumps({**out, "written": False, "error": error}))
            return 1
        env = data.get("env")
        if not isinstance(env, dict):
            env = {}
        previous = env.get(args.key) if args.key in env else None
        env[args.key] = args.value
        data["env"] = env
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        except OSError as exc:
            print(json.dumps({**out, "written": False, "error": str(exc)}))
            return 1
        print(json.dumps({**out, "written": True, "previous": previous,
                          "value": args.value}))
        return 0

    # restore
    try:
        state = json.loads(pathlib.Path(args.state_file).read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(json.dumps({**out, "restored": False, "error": str(exc)}))
        return 1
    if not state.get("readable", True):
        print(json.dumps({**out, "restored": False, "error": "no readable snapshot"}))
        return 1

    data, error = read()
    if error is not None:
        print(json.dumps({**out, "restored": False, "error": error}))
        return 1
    env = data.get("env")
    if not isinstance(env, dict):
        env = {}
    if state.get("present"):
        env[args.key] = state.get("value")
        action = "reinstated"
    else:
        env.pop(args.key, None)
        action = "removed"
    if env:
        data["env"] = env
    else:
        data.pop("env", None)
    try:
        if not state.get("file_existed") and _looks_empty(data):
            if path.exists():
                path.unlink()
            print(json.dumps({**out, "restored": True, "action": "removed-file"}))
            return 0
        path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        print(json.dumps({**out, "restored": False, "error": str(exc)}))
        return 1
    print(json.dumps({**out, "restored": True, "action": action}))
    return 0


def cmd_mcp_registered(args):
    """Is <name> registered in one *specific* scope?

    `claude mcp get` resolves across all three scopes, so it cannot tell a
    project-scoped registration this skill owns from a user-scoped one it must
    not touch — and answering the wrong question turns "we created this" into
    "we replaced someone else's". Read the file the scope actually writes.

    Always exits 0. "registered" is true, false, or null when the config exists
    but cannot be read; the caller decides what to do with an unknown, and the
    conservative choice is to assume something was there.

    --env-key and --has-arg answer "how was it registered?" as structured
    fields, because the flattened `args`/`env` strings are only fit for printing.
    Substring-matching them is not an exact check and reads as one: with
    LOOGLE_URL pinned to http://127.0.0.1:1, the string form is satisfied by
    NOTE=LOOGLE_URL=http://127.0.0.1:1-suffix (a different variable entirely)
    and by LOOGLE_URL=http://127.0.0.1:10 (a different port), while
    `--loogle-local=false` contains `--loogle-local`. All three are exactly the
    fallback-capable registrations the check exists to catch.
    """
    path = _mcp_config_path(args.scope, args.repo_root)

    # Everything from the stat onwards is caught: an unreadable file, a
    # permission error on a parent, a bad encoding, and a config whose shape is
    # not what it should be all mean the same thing here — we cannot tell. The
    # "always exits 0" contract has to hold against all of them, not just
    # against malformed JSON.
    out = {"name": args.name, "scope": args.scope, "source": str(path)}
    try:
        if not path.is_file():
            out["registered"] = False
        else:
            data = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(data, dict):
                raise ValueError("config root is not a JSON object")
            servers = _mcp_servers(data, args.scope, args.repo_root)
            if servers is None:
                servers = {}
            out["registered"] = args.name in servers
            if out["registered"]:
                entry = servers[args.name]
                # An entry that is not an object is a registration we cannot
                # read. Say so as a field: the key really is present, so
                # reporting "not registered" would be a lie, and every "how was
                # it registered" answer below has to fail closed.
                out["entry_object"] = isinstance(entry, dict)
                argv, env = [], {}
                if isinstance(entry, dict):
                    if isinstance(entry.get("args"), list):
                        argv = [str(a) for a in entry["args"]]
                    if isinstance(entry.get("env"), dict):
                        env = entry["env"]
                # The command matters as much as the arguments: an entry naming
                # the right flags on the wrong binary is not this skill's server.
                command = entry.get("command") if isinstance(entry, dict) else None
                out["command"] = "" if command is None else str(command)
                # Flattened forms, for printing only. Never match against these.
                out["args"] = " ".join(argv)
                out["env"] = " ".join("%s=%s" % (k, v) for k, v in sorted(env.items()))

                # Comparing basenames answers "is it named right", not "is it
                # the executable we installed". A shim called lean-lsp-mcp
                # earlier on PATH, or a leftover registration pointing into a
                # venv that has since been replaced, both pass a basename test
                # and neither is this skill's server. realpath settles it.
                out["command_realpath"] = (
                    str(pathlib.Path(out["command"]).resolve(strict=False))
                    if out["command"] else ""
                )
                if args.expect_command:
                    want = str(pathlib.Path(args.expect_command).resolve(strict=False))
                    out["expect_command_realpath"] = want
                    out["command_exact"] = out["command_realpath"] == want

                # Set membership cannot see order, and order is meaningful:
                # `--lean-project-path --repl` parses `--repl` as the project
                # path. Compare the vector as written.
                if args.expect_argv is not None:
                    out["expect_args"] = " ".join(args.expect_argv)
                    out["argv_exact"] = argv == args.expect_argv
                if args.require_arg:
                    out["missing_args"] = " ".join(a for a in args.require_arg if a not in argv)
                if args.opt_value is not None:
                    # The element *after* an option, e.g. --lean-project-path DIR.
                    out["opt"] = args.opt_value
                    out["opt_present"] = args.opt_value in argv
                    i = argv.index(args.opt_value) if args.opt_value in argv else -1
                    out["opt_value"] = argv[i + 1] if 0 <= i < len(argv) - 1 else None
                if args.has_arg is not None:
                    out["arg"] = args.has_arg
                    out["has_arg"] = args.has_arg in argv     # exact element
                if args.env_key is not None:
                    out["env_key"] = args.env_key
                    out["env_present"] = args.env_key in env
                    value = env.get(args.env_key)
                    out["env_value"] = None if value is None else str(value)

                # Does the *registered* PATH resolve the subprocesses the server
                # shells out to? Claude Code spawns MCP servers without a login
                # shell, so a PATH that works in the terminal running this check
                # says nothing about the one the server will actually get. This
                # asks the registration itself, so the answer does not depend on
                # the environment the verifier happens to be running in.
                if args.env_path_find:
                    raw = env.get(args.env_path_key)
                    dirs = str(raw).split(os.pathsep) if isinstance(raw, str) else []
                    out["env_path_value"] = raw if isinstance(raw, str) else None
                    out["env_path_dirs"] = len(dirs)
                    missing = []
                    for name in args.env_path_find:
                        for d in dirs:
                            cand = pathlib.Path(d) / name
                            if cand.is_file() and os.access(str(cand), os.X_OK):
                                break
                        else:
                            missing.append(name)
                    out["env_path_missing"] = " ".join(missing)
    except (OSError, ValueError, TypeError, AttributeError) as exc:
        out["registered"] = None
        out["error"] = str(exc)
    print(json.dumps(out))
    return 0


# Which actions mean "this component would not be here but for the skill".
# In-flight actions count: a half-finished install is still the skill's mess.
_SKILL_ACTIONS = {"installed", "installing"}

# Components that live outside the project and are shared with every other
# project and tool on the machine. The skill may well have triggered the
# download, but "we caused it" does not make it ours to delete, so they get a
# distinct origin rather than being silently left out of the record.
#
# The test is *where it lives*, not who fetched it. Everything under a
# machine-wide cache is reachable by any project on the host, and this manifest
# records one project: it has no way to know whether another project is using
# the same artefact, and there is no reference count anywhere to consult. Absent
# that, the conservative classification is the only safe one — a wrong `shared`
# leaves a stale directory, a wrong `skill` deletes a working install out from
# under another project.
#
#   lean_toolchain       ~/.elan/toolchains/<version>          per toolchain
#   hf_*_model           ~/.cache/huggingface                  machine-wide
#   lean_explore_data    ~/.lean_explore/cache/<version>       machine-wide
#   loogle_repo/_binary  ~/.cache/lean-lsp-mcp/loogle/repo-*   per (ref, toolchain)
#
# `loogle_index` is deliberately NOT here: it is keyed on sha256 of the resolved
# project path, so it belongs to exactly one project and nothing else can be
# using it.
_SHARED_COMPONENTS = {
    "lean_toolchain",
    "hf_embedding_model",
    "hf_reranker_model",
    "lean_explore_data",
    "loogle_repo",
    "loogle_binary",
}


def _merge_provenance(old, fresh):
    """Merge provenance component by component, preserving *origin*.

    Provenance answers a question about the whole history of the install, not
    about the last run: may an uninstall remove this? Recording only what the
    latest run observed loses that. A run that installs uv writes `installed`;
    the next run sees uv already present and writes `preexisting`, and the fact
    that the skill created it is gone after one repair.

    So each component carries a sticky `origin` — `skill` if the skill brought
    it into existence, `user` if it predated the skill — alongside `action`,
    what the latest run did. Origin is derived once, from the first action ever
    recorded, and never overwritten afterwards.

    The one reset is `absent`: if the component is not there, the next run's
    observation starts fresh, so a user who reinstalls it by hand is not
    recorded as `skill` on the strength of an install that is long gone.

    Entries are merged, never cleared by stage: a stage that ran and failed
    reports nothing, and dropping its history on that basis would erase the
    record of what an earlier run created — precisely when it matters most.
    """
    def normalise(entry):
        # 0.2.x wrote a bare action string, and a hand-edited manifest may too.
        # The action vocabulary did not change, so the origin follows from it.
        if isinstance(entry, dict):
            return dict(entry)
        return {"action": str(entry)}

    def origin_for(action, prior):
        if action == "absent":
            return None                      # nothing there: the next run re-derives
        if action in _SKILL_ACTIONS:
            # install.sh only chooses these when its before-state check found
            # the component missing, so this run created what is there now —
            # whatever an older, since-removed copy used to belong to.
            return "skill"
        return prior or "user"

    old = {k: normalise(v) for k, v in old.items()} if isinstance(old, dict) else {}
    fresh = fresh if isinstance(fresh, dict) else {}

    # 0.3.x keyed MCP registrations without a scope. Leaving those behind would
    # strand real history under a key nothing writes any more. They cannot be
    # folded into the current scope either: the scope they referred to was never
    # recorded, and guessing it wrong is how a user-scoped registration inherits
    # a skill origin. Retire them to an explicit `.unknown` scope instead —
    # visibly not a real scope, and still a record that something exists.
    # Named exactly, not matched by prefix. `mcp_*` is not a namespace reserved
    # for registrations — `mcp_timeout` (a settings-file mutation, no scope of
    # its own) matched a `startswith("mcp_")` guard here and was retired to a
    # scope it never had, on its first run.
    for name in [k for k in ("mcp_lean_lsp", "mcp_lean_explore") if k in old]:
        entry = old.pop(name)
        entry.setdefault("scope", "unknown")
        old.setdefault(name + ".unknown", entry)

    # Derive the recorded history's origins *first*. A 0.2.x entry that this
    # run also touches has to contribute its own origin before the new action
    # overwrites the old one — otherwise migrating and touching in the same run
    # silently downgrades a skill-owned component to `user`.
    for entry in old.values():
        if "origin" not in entry:
            derived = origin_for(entry.get("action"), None)
            if derived:
                entry["origin"] = derived

    merged = dict(old)
    for name, raw in fresh.items():
        entry = normalise(raw)
        action = entry.get("action")
        origin = origin_for(action, old.get(name, {}).get("origin"))

        out = {"action": action}
        if origin:
            out["origin"] = origin
        if entry.get("scope"):
            out["scope"] = entry["scope"]
        merged[name] = out

    # Caches shared with every other project and tool on the machine. Whoever
    # triggered the download, they are never one project's to delete.
    for name, entry in merged.items():
        if name in _SHARED_COMPONENTS and entry.get("action") != "absent":
            entry["origin"] = "shared"
    return merged


def cmd_write_manifest(args):
    """Merge resolved values into the manifest.

    Stage ownership matters: a key owned by a stage that ran this time is
    overwritten even when the new value is null (the stage genuinely produced
    nothing), while keys owned by stages that did not run are preserved. A
    blind merge would leave stale pins behind after a component was removed.

    `--stages` lists the stages that ran *to completion*. A stage that started
    and then failed knows nothing reliable about its keys, so clearing them on
    its behalf would replace good recorded pins with nulls.

    Provenance does not use stage ownership at all — see _merge_provenance.
    """
    owners = {
        "mathlib": ["mathlib_rev", "mathlib_inputrev", "mathlib_url"],
        "repl": ["repl_rev", "repl_inputrev"],
        "leanlsp": ["lean_lsp_mcp"],
        "loogle": ["loogle_index"],
        "leanexplore": [
            "lean_explore",
            "lean_explore_data",
            "embedding_model",
            "embedding_revision",
            "reranker_model",
            "reranker_revision",
        ],
    }

    out = pathlib.Path(args.out)
    merged = {}
    if out.exists():
        try:
            merged = json.loads(out.read_text(encoding="utf-8"))
        except ValueError:
            merged = {}

    fresh = json.loads(args.values)
    ran = set(args.stages.split())

    # Always-current facts.
    for key in (
        "generated", "project", "lean_toolchain",
        "elan", "ripgrep", "uv", "skill_version",
        "stages_completed", "stages_incomplete",
    ):
        if key in fresh:
            merged[key] = fresh[key]

    # A stage that completed owns its keys outright. A stage that did not is
    # preserved, never *seeded*: install.sh emits its version constants on every
    # run regardless of which stages ran, so copying non-null values across
    # would have `--only register` assert that lean-lsp-mcp 0.29.0 and
    # lean-explore 1.2.1 are installed when neither stage was even selected.
    for stage, keys in owners.items():
        if stage in ran:
            for key in keys:
                merged[key] = fresh.get(key)

    merged["provenance"] = _merge_provenance(merged.get("provenance"), fresh.get("provenance"))

    # Measurement attempts are appended, never merged.
    #
    # The previous shape was one flat object merged key by key, and that quietly
    # re-attributed history: the newer run's host and timestamp overwrote the
    # older run's, while the older run's per-stage figures were preserved beside
    # them, so a manifest could end up saying a Loogle index measured on host A
    # was measured on host B. The same held for pins — a Mathlib bump followed by
    # `--only register` left the old index cost sitting next to the new revision.
    #
    # Each record is self-contained (stage, timestamp, outcome, host, pins,
    # metrics), so records from different runs coexist without any of them
    # needing to be reconciled. A run that measured nothing appends nothing.
    #
    # Nothing reads these back to decide anything: no threshold, no later run, no
    # requirement. They are diagnostics and provenance.
    old_a = merged.get("measurement_attempts")
    old_a = old_a if isinstance(old_a, list) else []
    new_a = fresh.get("measurement_attempts")
    new_a = new_a if isinstance(new_a, list) else []
    if new_a or old_a:
        # A retention cap, not an estimate: an install run appends at most a
        # handful of records, and a manifest is a working file that a human
        # reads. The oldest records are dropped, never rewritten, so what remains
        # is still exactly what those runs observed.
        merged["measurement_attempts"] = (old_a + new_a)[-MAX_ATTEMPT_RECORDS:]

    # 0.9.0 and earlier wrote a flat `measurements` object with no per-figure
    # context. It cannot be converted into records — the host and pins each
    # figure belongs to were not recorded — so it is dropped rather than
    # reinterpreted. Guessing that context is precisely the defect.
    merged.pop("measurements", None)

    out.write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"written": str(out)}))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("require", help="read a [[require]] block from lakefile.toml")
    p.add_argument("project"); p.add_argument("name"); p.set_defaults(fn=cmd_require)

    p = sub.add_parser("resolved", help="read a resolved package from lake-manifest.json")
    p.add_argument("project"); p.add_argument("name"); p.set_defaults(fn=cmd_resolved)

    p = sub.add_parser("loogle-index", help="exact loogle index path for a project")
    p.add_argument("project"); p.add_argument("--cache-dir"); p.set_defaults(fn=cmd_loogle_index)

    p = sub.add_parser("mcp-entry", help="snapshot/restore one MCP registration")
    p.add_argument("action", choices=("get", "restore"))
    p.add_argument("name")
    p.add_argument("--scope", required=True, choices=("project", "local", "user"))
    p.add_argument("--repo-root", required=True)
    p.add_argument("--state-file", help="snapshot JSON, required for restore")
    p.set_defaults(fn=cmd_mcp_entry)

    p = sub.add_parser("settings-env", help="read/set/restore one env key in Claude settings")
    p.add_argument("action", choices=("get", "set", "restore"))
    p.add_argument("--key", required=True)
    p.add_argument("--value", help="required for set")
    p.add_argument("--repo-root", required=True)
    p.add_argument("--settings-file", help="override the settings.local.json path")
    p.add_argument("--state-file", help="snapshot JSON, required for restore")
    p.set_defaults(fn=cmd_settings_env)

    p = sub.add_parser("mcp-registered", help="is an MCP server registered in one scope?")
    p.add_argument("name")
    p.add_argument("--scope", required=True, choices=("project", "local", "user"))
    p.add_argument("--repo-root", required=True)
    p.add_argument("--env-key", help="report this env var exactly: env_present, env_value")
    p.add_argument("--has-arg", help="exact argv membership, as has_arg (use --has-arg=--flag)")
    p.add_argument("--require-arg", action="append", default=[],
                   help="repeatable; the absent ones come back in missing_args")
    p.add_argument("--opt-value", help="the argv element following this option, as opt_value")
    p.add_argument("--expect-command", help="compare the registered command by realpath")
    p.add_argument("--expect-argv", action="append",
                   help="repeatable, ordered; the whole argv is compared as argv_exact")
    p.add_argument("--env-path-key", default="PATH",
                   help="which env var --env-path-find searches (default PATH)")
    p.add_argument("--env-path-find", action="append", default=[],
                   help="repeatable; executables not resolvable in the registered "
                        "PATH come back in env_path_missing")
    p.set_defaults(fn=cmd_mcp_registered)

    p = sub.add_parser("hf-revision", help="cached snapshot revision of a HF model")
    p.add_argument("model"); p.set_defaults(fn=cmd_hf_revision)

    p = sub.add_parser("write-manifest", help="merge resolved values into the manifest")
    p.add_argument("--out", required=True)
    p.add_argument("--values", required=True, help="JSON object of resolved values")
    p.add_argument("--stages", default="", help="space-separated stages that ran")
    p.set_defaults(fn=cmd_write_manifest)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
