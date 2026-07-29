---
name: lean-kb-setup
description: Install, repair, and test the local Lean knowledge-base tooling for a Lean 4 + Mathlib project — lean-lsp-mcp (LSP tools, ripgrep local search, local Loogle index, Lean REPL) and LeanExplore with its prebuilt local semantic index — then register both as MCP servers. Use when asked to set up, install, reinstall, repair, or verify the Lean MCP tools, local Loogle, or the local LeanExplore index.
---

# Lean knowledge-base setup

Installs and verifies the **prerequisites** for `ma1` (Lean) knowledge-base work:
two MCP servers and their local indexes, configured so every index that *can* be
local *is* local. See `reference.md` for the component matrix, what each run
measures, and troubleshooting.

Targets Linux, macOS, and WSL2. Native Windows is not supported — local Loogle is
Unix-only; tell the user to work inside WSL2.

## Scope

This skill installs **stock upstream tooling**. It does **not** implement the
knowledge base described in [KB.md](../../../KB.md). Do not describe a successful
run as "the knowledge base is built".

What you get is a working Lean environment plus search over **Mathlib as
published upstream**. Specifically, KB.md requires all of the following, and none
of it is delivered here:

| KB.md requirement | Status after this skill |
|---|---|
| Project declarations in the search corpus | **absent** — the LeanExplore index is a prebuilt Mathlib snapshot; your own Lean code is not in it |
| One unified corpus over Mathlib + project code | **absent** — Loogle and LeanExplore are separate corpora with separate coverage |
| Source-reference / bibliography metadata | **absent** — no extraction, no schema, no query filter |
| Incremental indexing, atomic index publication | **absent** — LeanExplore data is fetched whole; Loogle re-indexes wholesale |
| A KB MCP tool over the unified corpus | **absent** — you get upstream's tools, not KB.md's |
| Reproducibility from pinned versions | **partial** — `.lean-kb-manifest.json` records resolved pins, but the LeanExplore corpus is a dated nightly unrelated to your Mathlib pin |

The one KB.md step this genuinely satisfies is the last link in its chain:
verifying retrieved declarations against a locally pinned Lean/Mathlib via
`lean-lsp-mcp`. Building the corpus itself is separate work — the extension point
is LeanExplore's own extraction pipeline, noted at the end of `reference.md`.

## What gets installed

| Component | Purpose | Local? |
|---|---|---|
| `uv` | runs both Python servers | — |
| `ripgrep` | required by `lean_local_search`, `lean_verify` | — |
| Mathlib | the corpus every local tool reads | yes |
| Lean REPL | fast `lean_run_code` / `lean_multi_attempt` | yes |
| `lean-lsp-mcp` | 16 LSP tools, local search, build | yes |
| local Loogle index | type/pattern search without the 3-req/30s remote limit | yes |
| `lean-explore[local]` + data | semantic search over Mathlib: prebuilt index + Qwen3 embedding model | yes |

Four `lean-lsp-mcp` tools stay remote because they have no local mode:
`lean_leansearch`, `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`.
The last two accept self-hosted backends via `LEAN_STATE_SEARCH_URL` / `LEAN_HAMMER_URL`.

## Procedure

Run the scripts in order from the repo root. They are idempotent — after a
failure, fix the cause and re-run the same command.

**1. Probe the host.** Never skip this: it finds the blockers that would
otherwise surface deep inside a long build — an unsupported platform, a missing
prerequisite, a moving Mathlib pin. It reports host resources as facts and
draws no verdict from them; this skill holds no resource thresholds.

```bash
bash .claude/skills/lean-kb-setup/scripts/preflight.sh --project lean
```

Read the output to the user, then act on it:

- **FAIL** — stop and report. These are hard blockers (unsupported OS, a missing
  `python3`/`git`/`curl`, no Lean project, no Mathlib tag for the toolchain), not
  things to work around silently.
- **WARN** — proceed, but tell the user which capability is degraded and what it
  would take to fix.
- **INFO** — a host fact with no verdict attached: RAM, swap, cores, free space,
  whether a first Loogle index is still ahead. Pass these on as observations.
  Do not turn them into a prediction about whether the install will succeed —
  that is what running it establishes.
- **needs approval** — a `sudo` command (only ripgrep needs one). Ask the user
  before running anything with `--allow-sudo`.

**2. Install.**

```bash
bash .claude/skills/lean-kb-setup/scripts/install.sh --project lean
```

Run it in the background: a cold Mathlib fetch plus a first Loogle index is the
longest part of the setup, and how long depends on the host, the network and
whether Mathlib's build cache hits. Useful flags: `--only STAGES` / `--skip STAGES` (stages listed in
`install.sh --help`), `--allow-sudo`, `--mcp-scope project|local|user` (default
`project`), `--le-data-version` to pin the LeanExplore corpus.

Version pins come from the project's own `lean-toolchain`; the script derives the
matching Mathlib and `repl` release tags. It **validates an existing pin** rather
than trusting it — a require on a moving branch is a hard error, because an
unpinned dependency defeats KB.md's reproducibility requirement.

`lake build` runs with Lake's own defaults, which means one `lean` worker per
core when `lake exe cache get` misses and Mathlib compiles from source. **Lake
5.0 has no `-j`/`--jobs` option** — `lake build -j 4` is `error: unknown short
option '-j'` — so on a high-core, memory-constrained host there is nothing to
turn down, and a cache miss can end at the OOM killer. The lever is the host.

The loogle stage runs the clone, build and index itself rather than triggering
them through a `lean_loogle` call, because that path wraps them in upstream's
fixed 900 s and 300 s timeouts. It measures the index step — exit status, signal,
elapsed time, peak RSS, cgroup OOM delta — so a failure is diagnosed from
evidence rather than inferred from the host's total RAM. It passes only when the
run reported readiness *and* answered a query; when it did not, one strict probe
gets to prove the index on disk still loads, and otherwise the stage stops. An
index file left by an earlier run is not evidence about this one.

The LeanExplore warm-up passes `rerank_top: 0`, so the readiness check does not
drag in a per-query cross-encoder pass. The Qwen3 **reranker** is still
prefetched by default, because nothing in the registration can stop a runtime
call from reranking — `mcp serve` has no such flag and the package reads no such
env var — and an unfetched model means that call downloads it mid-session.
`--no-rerank-prefetch` skips the download; `--rerank-check` additionally runs one
reranked query to prove it works.

The register stage also raises **Claude Code's MCP handshake budget**. With
`--loogle-local`, lean-lsp-mcp imports Mathlib *before* it answers the
handshake, and Claude Code abandons a server after 30000 ms — at which point
none of the 16 lean-lsp tools register. Whether the import fits inside that
depends on whether Mathlib's `.olean` files are in the page cache, which nothing
controls, so the same install works or fails by luck. `install.sh` writes
`env.MCP_TIMEOUT` into the project's `.claude/settings.local.json`, never
lowering a larger value already there; `--no-mcp-timeout` opts out. **Tell the
user this setting was changed, and why** — it alters how their Claude Code
behaves, not just this project's tooling. Claude reports the wait while it
happens, so a long budget costs nothing when the import is fast.

It writes `.lean-kb-manifest.json` recording the *resolved commits*, not just the
tags asked for, plus a `provenance` map giving each component a sticky
`origin` (`skill` or `user`) and the latest `action`. Consult it before removing
anything — it is the only record of the pre-install state. A run that aborts
partway still writes it, and `stages_incomplete` names what did not finish.

**3. Verify.**

```bash
bash .claude/skills/lean-kb-setup/scripts/verify.sh --project lean
```

Checks binaries, that Mathlib actually imports, both MCP handshakes, a real
query through each local index, and *how* each server was registered — a
`lean-lsp` without `--loogle-local` is a FAIL, not a pass. `--quick` skips the
full `import Mathlib` and the Loogle query when you only need a fast confidence
check. `--mcp-scope` must match whatever `install.sh` used (default `project`).

It also starts each server **from its own registration** — recorded command,
argv and env — under the PATH `verify.sh` was launched with rather than the one
it exports for itself. Reading a config is not the same as running it: on the
first VM run every config check passed while the server, spawned by Claude Code
without `~/.elan/bin`, could not find `lake`. Even so, only a real Claude
restart settles a registration; this is the closest a script can get.

**Expect a slow first query, and know which cost is which.** LeanExplore loads
its index and the embedding model lazily, on the first query rather than at
startup, so whichever query comes first pays for all of it — per server process,
not per install, so it recurs after every Claude restart. That is not a hang, and
it is not evidence about memory. A warm-up hook is under test as a remedy.

Reranking is a *different* cost and does not amortise: `rerank_top` defaults to
50 in both search tools, which is a cross-encoder pass on every call. Every probe
this skill runs passes `rerank_top: 0`; `verify.sh --rerank` tests the reranking
path deliberately. **Tell the user that callers must pass `rerank_top: 0`
explicitly** — the server side cannot be configured, so the call site is the only
lever. The project's `CLAUDE.md` is where that rule belongs.

`--skip SECTIONS` suppresses a section *and the binaries it owns*, so a staged
install can be verified as it goes: `--skip "leanlsp loogle leanexplore
register"` after `--only mathlib` passes without failing on tools that are
absent exactly as intended.

`install.sh` exits non-zero when any stage did not complete, even one that
carried on after a caught error. Do not read a zero exit as "all stages ran" —
read `stages_incomplete` in the manifest.

**4. Restart Claude Code** so it picks up the newly registered MCP servers, then
confirm with `claude mcp list`.

## Rules

- Report host limits, do not paper over them. There is no Loogle fallback at
  any layer: no index ⇒ `install.sh` stops; no `--loogle-local` ⇒ registration
  refuses; and registration pins `LOOGLE_URL` to a dead endpoint so an upstream
  runtime fallback raises instead of answering remotely. Never ship a setup the
  user believes is fully local when it is not. `--skip loogle` is the user's
  decision to make, not yours — ask first.
- A config you cannot parse is *unknown*, never *empty*. Registration is
  refused outright when the rollback snapshot is unreadable, because that is
  the one case where a failed write cannot be undone.
- **A server that starts is not a server that starts in time.** Claude Code
  gives an MCP handshake 30000 ms; lean-lsp-mcp with `--loogle-local` spends
  that importing Mathlib before it replies. No script can observe this by
  running the server, because it runs the server on its own budget — `verify.sh`
  passes identically at 9 s and at 103 s. The only checkable thing is whether
  the client was told to wait, so `verify.sh` FAILs when `MCP_TIMEOUT` is unset
  or short. When lean-lsp is missing after a restart, read
  `~/.cache/claude-cli-nodejs/<slug>/mcp-logs-lean-lsp/*.jsonl` — every
  connection logs its budget and its outcome with timestamps.
- **A server that works when you run it does not work when Claude runs it.**
  Claude Code spawns MCP servers without a login shell, so anything the server
  resolves from its environment has to be recorded in the registration itself:
  a `PATH` that finds `lake` and `git`, and `LEAN_LOOGLE_CACHE_DIR` naming the
  cache the index was actually built in. Never conclude a registration is sound
  from a probe that used your own environment; that is precisely what passed
  while the restarted server was failing. A genuine Claude restart is the only
  real test.
- **Never quote a resource figure as a requirement.** This skill holds no RAM,
  disk, download-size or timing constants, and derives no PASS/WARN/FAIL from
  one: they all move with upstream versions, models, queries and the host. Say
  what is expensive and why, run the operation, and report what *this* run
  measured — exit status, elapsed time, peak RSS, signal, cgroup OOM events,
  artefact size. The manifest's `measurement_attempts` are append-only records,
  each carrying the host and pins it was taken under: provenance for that run,
  never requirements for the next. Never quote one of them back as a threshold.
- Report the tool's own error text. `--quiet` suppresses stdout, never the
  server's account of what went wrong, and "it failed" plus a guess at the cause
  is a worse report than the one the server already handed you.
- **Do not assert an OOM.** Not from the host's RAM, not from a signal, and not
  from a missing artefact. The cgroup `oom_kill` counter is the only evidence
  here, and even it establishes that something *in that cgroup* was killed, not
  which process. Report what was observed and name `dmesg -T | grep -i oom` as
  what would settle the rest. `install.sh` captures status, signal, peak RSS and
  the counter for every expensive step it runs.
- **An artefact existing is not an artefact working.** The Loogle stage requires
  readiness and a real answer, not a file of the right name; a query answering is
  not proof the local index served it. Apply the same test to anything else you
  are tempted to call verified.
- Never pin Mathlib to a moving branch.
- Prefer `--only` over rerunning everything when repairing one component.
- Never claim this built a KB.md knowledge base. See **Scope** above.
- `lean-explore search` on the CLI is the **hosted API** and needs
  `LEANEXPLORE_API_KEY`. The local backend is reachable only via
  `lean-explore mcp serve --backend local`. Never use the CLI to test a local
  install — it verifies the wrong backend.
- A successful `lean_loogle` query does not prove local Loogle works: it falls
  back to the remote API silently. Only this project's own index file, at the
  path `introspect.py loogle-index` computes, is evidence.
- `introspect.py loogle-index` exits 0 whether or not the index exists — it
  answers "where would it be". Read its `exists` field, never its exit status.
- Only ever remove a component whose `provenance` entry says `origin: skill`.
  `origin: user` means the user had it before this skill ran, and nothing here
  can put back what a `replaced` action overwrote. `origin: shared` is a
  machine-wide cache (Lean toolchains, HuggingFace models) — never remove those
  on behalf of one project, whoever triggered the download.
- An `action` ending in `-ing` means that mutation never completed. Treat the
  component as possibly half-written and re-run its stage before trusting it.
