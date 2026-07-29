#!/usr/bin/env bash
# Test the installed stack end to end: binaries, Mathlib, both MCP servers, and
# a real query through each local index.
#
# Usage: verify.sh [--project DIR] [--quick] [--skip STAGES]
#                  [--mcp-scope project|local|user]
#
#   --quick  import one small Mathlib module instead of all of Mathlib, and
#            skip the Loogle query (which loads ~7 GiB of oleans)
#
# Exit 0 when nothing failed.
#
# A missing local Loogle index is a FAIL, not a warning. It still "works" —
# lean_loogle answers from the remote API — which is exactly why it has to be
# loud: a silent downgrade to a rate-limited remote service is the failure mode
# this whole check exists for. Use --skip loogle to opt out deliberately.

set -uo pipefail   # deliberately no -e: every check must run and be reported
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/common.sh"

PROJECT="$PWD"; QUICK=0; SKIP=""; MCP_SCOPE="project"
while [ $# -gt 0 ]; do
  case "$1" in
    --project) PROJECT="$2"; shift 2 ;;
    --quick)   QUICK=1; shift ;;
    --skip)    SKIP="$2"; shift 2 ;;
    --mcp-scope) MCP_SCOPE="$2"; shift 2 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) die "unknown argument: $1" ;;
  esac
done

# Sections --skip can actually suppress. Validated, so an ineffective value is
# an error rather than a silent no-op.
SKIPPABLE="mathlib leanlsp loogle leanexplore register"
for s in $SKIP; do
  case " $SKIPPABLE " in
    *" $s "*) ;;
    *) die "cannot skip '$s' — skippable sections: $SKIPPABLE" ;;
  esac
done

case "$MCP_SCOPE" in
  project|local|user) ;;
  *) die "invalid --mcp-scope '$MCP_SCOPE' — use project, local, or user" ;;
esac

skipped() { case " $SKIP " in *" $1 "*) return 0 ;; esac; return 1; }

# Kept as it was *before* the augmentation below, because that is roughly the
# environment Claude Code will spawn the MCP servers in: no login shell, no
# ~/.elan/bin. The registered-entry probe runs under it, so a server that only
# works thanks to this script's own PATH cannot pass.
ORIG_PATH="$PATH"
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"
PROJ="$(find_lean_project "$PROJECT")" || die "no Lean project at or above $PROJECT"

# ------------------------------------------------------------- binaries ----

section "Binaries"

# Version probes get a hard timeout. `lake --version` in particular can block
# for minutes: outside a Lean project elan resolves a *default* toolchain and
# will download one if none is installed.
#
# Probes run as argument vectors, never through `sh -c` with an interpolated
# project path — a path containing an apostrophe would otherwise break or
# inject shell syntax.
probe() { if have timeout; then timeout 60 "$@"; else "$@"; fi; }

# `report` is either the literal "version" — print the probe's first output line
# — or a label to print instead. Not every CLI has a --version: LeanExplore
# 1.2.1 does not, and probing for one guaranteed a FAIL on a working install.
# The probe still has to be side-effect free, so --help rather than a query.
check_bin() { # binary, required|optional, version|<label>, then the probe argv
  bin="$1"; requirement="$2"; report="$3"; shift 3
  if ! have "$bin"; then
    if [ "$requirement" = required ]; then fail "$bin not on PATH"; else warn "$bin not on PATH"; fi
    return
  fi
  # A probe that exits non-zero is a broken install, not a pass.
  if out="$(probe "$@" 2>/dev/null)"; then
    if [ "$report" = version ]; then
      pass "$bin $(printf '%s' "$out" | head -1)"
    else
      pass "$bin $report"
    fi
  else
    fail "$bin is on PATH but '$*' failed"
  fi
}

# A binary belongs to the section that installs it, so --skip has to reach it
# too. Otherwise a staged install — Mathlib first, tools afterwards — can never
# report success: `verify.sh --skip leanlsp` would still FAIL on a lean-lsp-mcp
# that is absent exactly as instructed. uv, ripgrep and lake are prerequisites
# of the whole stack, not of one section, so they stay unconditional.
check_bin_for() { # section, binary, required|optional, then the version argv
  _sec="$1"; shift
  if skipped "$_sec"; then note "$1 not checked (--skip $_sec)"; return; fi
  check_bin "$@"
}

check_bin uv required version uv --version
check_bin rg required version rg --version
check_bin_for leanlsp     lean-lsp-mcp required version lean-lsp-mcp --version
# LeanExplore 1.2.1 has no --version flag; --help is the side-effect-free probe
# that a broken install still fails. The pinned version is in the manifest, and
# the MCP query below is the check that actually matters.
check_bin_for leanexplore lean-explore optional "installed (1.2.1 exposes no --version)" \
              lean-explore --help

# lake runs from inside the project so elan uses its pinned toolchain. The cd
# happens in bash, so the path is never re-parsed by a shell.
if have lake; then
  if out="$( (cd "$PROJ" && probe lake --version) 2>/dev/null )"; then
    pass "lake $(printf '%s' "$out" | head -1)"
  else
    fail "lake is on PATH but 'lake --version' failed in $PROJ"
  fi
else
  fail "lake not on PATH"
fi

# -------------------------------------------------------------- Mathlib ----

if skipped mathlib; then
  section "Mathlib"
  note "skipped"
else
section "Mathlib"

if [ -d "$PROJ/.lake/packages/mathlib" ]; then
  pass "fetched into $PROJ/.lake/packages/mathlib"

  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  if [ "$QUICK" -eq 1 ]; then
    printf 'import Mathlib.Logic.Basic\nexample : True := trivial\n' >"$tmp/Probe.lean"
    what="Mathlib.Logic.Basic"
  else
    printf 'import Mathlib\nexample : True := trivial\n' >"$tmp/Probe.lean"
    what="all of Mathlib"
  fi

  if out="$( (cd "$PROJ" && lake env lean "$tmp/Probe.lean") 2>&1 )"; then
    pass "$what imports and elaborates"
  else
    fail "importing $what failed"
    note "$(printf '%s' "$out" | head -5)"
  fi
else
  fail "Mathlib not fetched — run install.sh --only mathlib"
fi

if [ -d "$PROJ/.lake/packages/repl" ] || [ -d "$PROJ/.lake/packages/REPL" ]; then
  pass "Lean REPL present (fast lean_run_code / lean_multi_attempt)"
else
  warn "Lean REPL absent — those tools fall back to the slower LSP path"
fi

fi

# --------------------------------------------------------- lean-lsp-mcp ----

if skipped leanlsp; then
  section "lean-lsp MCP server"
  note "skipped"
else
section "lean-lsp MCP server"

LSP_CORE="lean_goal,lean_diagnostic_messages,lean_hover_info,lean_local_search,lean_loogle,lean_build"

if have lean-lsp-mcp; then
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 300 --expect-tools "$LSP_CORE" \
              -- lean-lsp-mcp --lean-project-path "$PROJ" 2>&1)"; then
    pass "handshake ok, core tools present"
    note "$(printf '%s' "$out" | sed -n '2p' | cut -c1-160)"
  else
    fail "handshake or tools/list failed"
    note "$(printf '%s' "$out" | tail -3)"
  fi

  # Proves ripgrep wiring and project resolution, not just that the server boots.
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 300 --quiet \
              --call lean_local_search --args '{"query": "Nat.add_comm", "limit": 3}' \
              -- lean-lsp-mcp --lean-project-path "$PROJ" 2>&1)"; then
    pass "lean_local_search returned matches"
  else
    fail "lean_local_search failed (ripgrep missing, or Mathlib not built)"
    note "$(printf '%s' "$out" | tail -3)"
  fi
else
  fail "lean-lsp-mcp not installed"
fi

fi

# --------------------------------------------------------- local Loogle ----

if skipped loogle; then
  section "Local Loogle index"
  note "skipped"
else
section "Local Loogle index"

# Both artefacts are keyed, and on different things: the index on sha256 of the
# resolved project path, the checkout on sha256 of the toolchain string. A glob
# over the cache matches *another* project's index and another toolchain's
# binary — and `--quick`, which stops after the structural checks, would then
# report a binary present purely because some unrelated checkout exists.
# Ask for this project's, on both counts.
#
# `loogle-index` exits 0 whether or not the files are there — computing a path
# is a different question from whether it exists — so the answers are in
# "exists" and "binary_exists". Reading the exit status instead would report
# every missing index as present.
cache=""; bin=""; idx=""; expected=""
if idx_json="$(python3 "$HERE/introspect.py" loogle-index "$PROJ" 2>/dev/null)"; then
  cache="$(printf '%s' "$idx_json" | jget cache_dir)"
  expected="$(printf '%s' "$idx_json" | jget path)"
  if [ "$(printf '%s' "$idx_json" | jget exists)" = "True" ]; then idx="$expected"; fi
  if [ "$(printf '%s' "$idx_json" | jget binary_exists)" = "True" ]; then
    bin="$(printf '%s' "$idx_json" | jget binary)"
  fi
else
  warn "could not compute the loogle paths for this project"
fi

if [ -n "$bin" ]; then
  pass "binary built for this toolchain: $bin"
else
  fail "no loogle binary for this project's toolchain"
  other="$(ls -1d "$cache"/repo-*/.lake/build/bin/loogle 2>/dev/null | wc -l | tr -d ' ')"
  if [ "${other:-0}" != "0" ]; then
    note "$other checkout(s) exist for other toolchains; the server will not use them"
  fi
fi

if [ -n "$idx" ]; then
  pass "index for THIS project present: $(du -h "$idx" | awk '{print $1}')"
elif [ -n "$bin" ]; then
  fail "binary built but this project has no index — first indexing run likely OOMed"
  note "expected at ${expected:-$cache/index/mathlib-<project-hash>.idx}"
  note "lean_loogle is silently answering from the remote API (3 req/30s)"
  other="$(ls -1 "$cache"/index/*.idx 2>/dev/null | wc -l | tr -d ' ')"
  [ "$other" != "0" ] && note "$other index file(s) exist for other projects; they do not apply here"
else
  fail "local Loogle not installed — lean_loogle is using the remote API (3 req/30s)"
  note "run install.sh --only loogle, or verify.sh --skip loogle to opt out deliberately"
fi

if [ -n "$idx" ] && [ "$QUICK" -eq 0 ] && ! skipped loogle; then
  # LOOGLE_URL is pinned to the dead endpoint for the probe too. Without it,
  # an index that exists but cannot be loaded makes upstream catch the local
  # exception and answer from loogle.lean-lang.org — and this check prints PASS
  # for a query that never touched the local index. The file existing is not
  # evidence that it loads.
  if out="$(LEAN_LOOGLE_LOCAL=true LOOGLE_URL="$LOOGLE_NULL_BACKEND" \
            python3 "$HERE/mcp_smoke.py" --timeout 600 --quiet \
              --call lean_loogle --args '{"query": "Nat.add_comm", "num_results": 3}' \
              -- lean-lsp-mcp --lean-project-path "$PROJ" --loogle-local 2>&1)"; then
    pass "lean_loogle answered from the local index (remote endpoint was dead)"
  else
    fail "lean_loogle query failed despite the index being present"
    note "$(printf '%s' "$out" | tail -3)"
  fi
fi

fi

# --------------------------------------------------------- lean-explore ----

if skipped leanexplore; then
  section "LeanExplore local index"
  note "skipped"
else
section "LeanExplore local index"

active="$HOME/.lean_explore/active_version"
if [ -f "$active" ] && [ -f "$HOME/.lean_explore/cache/$(cat "$active")/lean_explore.db" ]; then
  v="$(cat "$active")"
  pass "data toolchain $v ($(du -sh "$HOME/.lean_explore/cache/$v" | awk '{print $1}'))"
else
  fail "no local data — run install.sh --only leanexplore"
fi

if have lean-explore; then
  # Deliberately NOT `lean-explore search`: that subcommand builds an ApiClient
  # and needs LEANEXPLORE_API_KEY, so it would test the hosted API — the exact
  # backend this install is meant to avoid. The local backend is only reachable
  # through the MCP server.
  LE_CORE="search,search_summary,get_source_code,get_docstring,get_dependencies"
  if out="$(python3 "$HERE/mcp_smoke.py" --timeout 600 --quiet --expect-tools "$LE_CORE" \
              --call search_summary --args '{"query": "commutativity of addition", "limit": 3}' \
              -- lean-explore mcp serve --backend local 2>&1)"; then
    pass "MCP server answered a semantic query from the local backend"
  else
    fail "lean-explore MCP server failed"
    note "$(printf '%s' "$out" | tail -3)"
  fi
else
  fail "lean-explore not installed"
fi

fi

# ------------------------------------------------------------- Claude CC ----

if skipped register; then
  section "Claude Code registration"
  note "skipped"
else
section "Claude Code registration"

# Scope-exact, and it reads *how* each server was registered. `claude mcp list`
# resolves across scopes and says nothing about arguments, so it would report a
# PASS for a lean-lsp registered without --loogle-local — a working server
# quietly pointed at the remote Loogle API, which is the thing being tested.
ROOT="$(git -C "$PROJ" rev-parse --show-toplevel 2>/dev/null || echo "$PROJ")"

# Every fact comes back as a structured field. The `args`/`env` strings the same
# call returns are flattened with spaces and `=`, so substring tests on them are
# not the exact checks they look like: NOTE=LOOGLE_URL=<pin> satisfies a search
# for the pin while LOOGLE_URL itself is unset, <pin> is a prefix of a different
# port, and `--loogle-local=false` contains `--loogle-local`. Each of those is a
# live remote fallback that would be reported as PASS.
#
# `info` is left set for the caller, which reads the per-server fields it asked
# for. PASS is printed only once *everything* structural holds — announcing "it
# is registered" before validating the entry is how an unreadable or wrongly
# built registration slips through a run that then exits 0.
check_registration() { # name, expected binary, then extra introspect flags
  _name="$1"; _bin="$2"; shift 2
  info="$(python3 "$HERE/introspect.py" mcp-registered "$_name" \
            --scope "$MCP_SCOPE" --repo-root "$ROOT" "$@" 2>/dev/null)"

  case "$(printf '%s' "$info" | jget registered)" in
    True) ;;
    False) fail "$_name not registered in $MCP_SCOPE scope — run install.sh --only register"
           return 1 ;;
    # Not a warning: an unreadable config means this script cannot assert the
    # thing it exists to assert, and warnings do not affect the exit status.
    *)     fail "cannot read the $MCP_SCOPE MCP config for $_name — nothing here is verified"
           note "$(printf '%s' "$info" | jget error)"
           return 1 ;;
  esac

  if [ "$(printf '%s' "$info" | jget entry_object)" != True ]; then
    fail "the $_name entry in $MCP_SCOPE scope is not a JSON object — it cannot start"
    note "re-run install.sh --only register"
    return 1
  fi

  # A registration naming the right flags on the wrong binary is not this
  # skill's server, however well-formed it looks. Basenames are not enough for
  # that: a shim called lean-lsp-mcp somewhere else on disk, or an entry left
  # pointing into a venv that has since been replaced, both have the right
  # basename. When the binary is resolvable here, compare resolved paths.
  _cmd="$(printf '%s' "$info" | jget command)"
  if [ "$(basename "$_cmd")" != "$_bin" ]; then
    fail "$_name is registered to run '${_cmd:-(no command)}', not $_bin"
    note "re-run install.sh --only register"
    return 1
  fi
  case "$(printf '%s' "$info" | jget command_exact)" in
    True)  pass "$_name command resolves to the installed $_bin" ;;
    False) fail "$_name is registered to a different $_bin than the installed one"
           note "registered: $(printf '%s' "$info" | jget command_realpath)"
           note "installed:  $(printf '%s' "$info" | jget expect_command_realpath)"
           note "re-run install.sh --only register"
           return 1 ;;
    *) ;;  # not asked, or the binary is not on PATH here to compare against
  esac

  # From here the entry is inspectable, so every remaining problem is *reported*
  # rather than returned. Bailing out on the first one suppressed the specific
  # diagnoses that follow — a wrong argv would hide a missing PATH, and the
  # missing PATH is the more actionable finding of the two. The exit status
  # comes from the FAIL count, so nothing is softened by continuing.
  _ok=0

  _miss="$(printf '%s' "$info" | jget missing_args)"
  if [ -n "$_miss" ]; then
    _ok=1
    fail "$_name registered without: $_miss"
    note "args: $(printf '%s' "$info" | jget args)"
    note "re-run install.sh --only register"
  fi

  # Membership cannot see order, and order carries meaning: with the vector
  # `--lean-project-path --repl`, every required argument is present and the
  # project path is the string "--repl".
  case "$(printf '%s' "$info" | jget argv_exact)" in
    True)  pass "$_name argv matches what install.sh registers, in order" ;;
    False) _ok=1
           fail "$_name argv differs from what install.sh registers"
           note "registered: $(printf '%s' "$info" | jget args)"
           note "expected:   $(printf '%s' "$info" | jget expect_args)"
           note "re-run install.sh --only register" ;;
    *) ;;
  esac

  # Only once nothing structural is outstanding. Announcing "it is registered"
  # ahead of the checks is how a malformed entry used to slip through a run
  # that then exited 0.
  if [ "$_ok" -eq 0 ]; then
    pass "$_name registered ($MCP_SCOPE scope): $_cmd"
  fi
  return 0
}

# Start the server from its own registration — the recorded command, argv and
# env, under the PATH this script was launched with rather than the one it
# exported for itself. Every other check here reads the config; this one is the
# only evidence that what is written there can actually run. It is still not
# proof: Claude Code's own environment may differ again, so a genuine restart
# remains the last word.
smoke_registered() { # name, tool to call, JSON args, timeout
  _rname="$1"; _rcall="$2"; _rargs="$3"; _rto="$4"
  _spec="$(mktemp)"
  if ! python3 "$HERE/introspect.py" mcp-entry get "$_rname" \
         --scope "$MCP_SCOPE" --repo-root "$ROOT" >"$_spec" 2>/dev/null \
     || [ "$(jget readable <"$_spec")" != True ] \
     || [ "$(jget present <"$_spec")" != True ]; then
    rm -f "$_spec"
    return 1
  fi
  if out="$(PATH="$ORIG_PATH" python3 "$HERE/mcp_smoke.py" --timeout "$_rto" --quiet \
              --entry-file "$_spec" --call "$_rcall" --args "$_rargs" 2>&1)"; then
    pass "$_rname answers $_rcall when started exactly as registered"
    rm -f "$_spec"
    return 0
  fi
  fail "$_rname does not work when started as registered (env: the caller's PATH)"
  note "this is the failure a restarted Claude Code sees; the shell you ran"
  note "verify.sh in may still work, which is why this is checked separately"
  # One note per line: the server's own error text is usually several lines,
  # and a single note prints the rest unindented against the left margin.
  printf '%s\n' "$out" | tail -5 | while IFS= read -r _l; do note "$_l"; done
  rm -f "$_spec"
  return 1
}

# --loogle-local is queried separately from the required set so a missing flag
# gets its own diagnosis rather than a generic "registered without".
#
# An array, not a string: --expect-argv carries the project path, and word
# splitting would break the moment that path contained a space.
LSP_Q=(--require-arg=--repl --opt-value=--lean-project-path
       --env-key=LOOGLE_URL --has-arg=--loogle-local
       --env-path-key=PATH --env-path-find=lake --env-path-find=git
       --expect-argv=--lean-project-path "--expect-argv=$PROJ" --expect-argv=--repl)
if skipped loogle; then
  # `--skip loogle` means "do not judge the Loogle configuration", not "it must
  # be absent" — the user may have skipped the section on a machine where the
  # index is present and registered. Take the flag as it stands so the ordering
  # check still runs over the rest of the vector instead of failing on a
  # registration that is entirely correct.
  if [ "$(python3 "$HERE/introspect.py" mcp-registered lean-lsp --scope "$MCP_SCOPE" \
            --repo-root "$ROOT" --has-arg=--loogle-local 2>/dev/null | jget has_arg)" = True ]; then
    LSP_Q+=(--expect-argv=--loogle-local)
  fi
else
  LSP_Q+=(--expect-argv=--loogle-local)
fi
# Only when the binary is here to compare against; on a host where it is not
# installed, "not registered to the installed one" is not a finding.
lsp_installed="$(command -v lean-lsp-mcp 2>/dev/null || true)"
if [ -n "$lsp_installed" ]; then LSP_Q+=("--expect-command=$lsp_installed"); fi

if check_registration lean-lsp lean-lsp-mcp "${LSP_Q[@]}"; then
  # A server pointed at a *different* Lean project answers every query happily
  # and about the wrong code, so the path is compared exactly, not merely present.
  p="$(printf '%s' "$info" | jget opt_value)"
  if [ "$(printf '%s' "$info" | jget opt_present)" != True ]; then
    fail "registered without --lean-project-path — the server will guess a project"
  elif [ "$p" = "$PROJ" ]; then
    pass "--lean-project-path is this project"
  else
    fail "--lean-project-path is '$p', not the project being verified"
    note "expected $PROJ"
  fi

  if ! skipped loogle; then
    case "$(printf '%s' "$info" | jget has_arg)" in
      True) pass "registered with --loogle-local" ;;
      *) fail "registered WITHOUT --loogle-local — lean_loogle is on the remote API"
         note "args: $(printf '%s' "$info" | jget args)"
         note "run install.sh --only register, or --skip loogle to accept remote deliberately" ;;
    esac

    # The exact endpoint, and a FAIL rather than a WARN: warnings do not affect
    # the exit status, so a fallback-capable registration would still exit 0.
    # Any reachable LOOGLE_URL — the public service most of all — leaves the
    # runtime fallback open, which is the whole point of pinning it.
    url="$(printf '%s' "$info" | jget env_value)"
    if [ "$(printf '%s' "$info" | jget env_present)" != True ]; then
      fail "LOOGLE_URL not set — an upstream runtime failure falls back to the remote API silently"
      note "re-run install.sh --only register to pin it"
    elif [ "$url" = "$LOOGLE_NULL_BACKEND" ]; then
      pass "LOOGLE_URL pinned to the dead endpoint; a runtime fallback cannot pass unnoticed"
    else
      fail "LOOGLE_URL is set to something reachable — the runtime fallback is still open"
      note "expected $LOOGLE_NULL_BACKEND; found $url"
    fi

    # Which cache the server will read. Upstream resolves it from
    # LEAN_LOOGLE_CACHE_DIR / XDG_CACHE_HOME / ~/.cache at *runtime*, in the
    # environment Claude Code spawns it with — not the one that built the index.
    # A separate introspect call because --env-key reports one key at a time,
    # and the diagnosis for this one is nothing like the LOOGLE_URL diagnosis.
    cinfo="$(python3 "$HERE/introspect.py" mcp-registered lean-lsp \
               --scope "$MCP_SCOPE" --repo-root "$ROOT" \
               --env-key LEAN_LOOGLE_CACHE_DIR 2>/dev/null)"
    cval="$(printf '%s' "$cinfo" | jget env_value)"
    # Self-contained: recomputed here rather than borrowed from the Loogle
    # section, whose variables only exist when that section ran.
    cwant="$(python3 "$HERE/introspect.py" loogle-index "$PROJ" 2>/dev/null | jget path)"
    if [ "$(printf '%s' "$cinfo" | jget env_present)" != True ]; then
      fail "LEAN_LOOGLE_CACHE_DIR not set — the server resolves the cache from its own environment"
      note "it may look in a directory this install never built into, and fall back to the remote API"
      note "re-run install.sh --only register"
    elif [ -n "$cval" ] && [ -f "$cval/index/$(basename "${cwant:-x}")" ]; then
      # The registered directory demonstrably holds this project's index. That
      # is the question worth asking — comparing it against a path recomputed in
      # *this* shell would report a mismatch whenever XDG_CACHE_HOME differs
      # between the two environments, which is a difference, not a defect.
      pass "LEAN_LOOGLE_CACHE_DIR holds this project's index: $cval"
    else
      fail "LEAN_LOOGLE_CACHE_DIR does not contain this project's index"
      note "registered: ${cval:-(empty)}"
      note "no index at ${cval%/}/index/$(basename "${cwant:-<unknown>}")"
      note "re-run install.sh --only loogle register"
    fi
  fi

  # The registration's own PATH, resolved against the filesystem. Claude Code
  # starts this server without a login shell, so a PATH that works in the shell
  # running verify.sh proves nothing about the one the server gets. Asking the
  # registration makes the answer independent of this script's environment,
  # which is what the earlier version got wrong: it probed with its own PATH
  # and passed a registration that could not start lake at all.
  dirs="$(printf '%s' "$info" | jget env_path_dirs)"
  pmiss="$(printf '%s' "$info" | jget env_path_missing)"
  if [ -z "$dirs" ] || [ "$dirs" = 0 ]; then
    fail "no PATH in the registration — the server gets whatever Claude Code was started with"
    note "lean-lsp-mcp runs lake and git as subprocesses; without them local Loogle"
    note "fails at runtime and falls through to the remote API"
    note "re-run install.sh --only register"
  elif [ -n "$pmiss" ]; then
    fail "the registered PATH cannot resolve: $pmiss"
    note "PATH ($dirs entries): $(printf '%s' "$info" | jget env_path_value)"
    note "re-run install.sh --only register"
  else
    pass "the registered PATH resolves lake and git ($dirs entries)"
  fi

  # And then actually start it that way. Cheap relative to the rest, and it is
  # the only check here that exercises the registration rather than reading it.
  if ! skipped loogle && [ "$QUICK" -eq 0 ]; then
    smoke_registered lean-lsp lean_loogle \
      '{"query": "Nat.add_comm", "num_results": 3}' 600 || true
  else
    smoke_registered lean-lsp lean_local_search \
      '{"query": "Nat.add_comm", "limit": 3}' 300 || true
  fi
fi

# `lean-explore mcp serve --backend local`. The backend is the whole point: the
# same binary registered without it, or with the hosted backend, needs
# LEANEXPLORE_API_KEY and answers from the network.
LE_Q=(--require-arg=mcp --require-arg=serve --opt-value=--backend
      --expect-argv=mcp --expect-argv=serve --expect-argv=--backend --expect-argv=local)
le_installed="$(command -v lean-explore 2>/dev/null || true)"
if [ -n "$le_installed" ]; then LE_Q+=("--expect-command=$le_installed"); fi

if check_registration lean-explore lean-explore "${LE_Q[@]}"; then
  b="$(printf '%s' "$info" | jget opt_value)"
  if [ "$b" = local ]; then
    pass "--backend local; queries are served from the local index"
  else
    fail "registered with --backend '${b:-(unset)}', not local — this is the hosted API"
    note "args: $(printf '%s' "$info" | jget args)"
  fi

  # No PATH is registered for this one: it loads its models in-process and
  # shells out to nothing, so there is no subprocess to lose. Only lean-lsp
  # needs the pin.
  if [ "$QUICK" -eq 0 ]; then
    smoke_registered lean-explore search_summary \
      '{"query": "commutativity of addition", "limit": 3}' 600 || true
  fi
fi

if ! have claude; then
  note "claude CLI missing, but the config files were read directly"
fi

fi

summary "Verify"
