# Lean REPL — Main Agent

This file is for the main agent only. Subagents read `LEAN_REPL_GENERAL.md`.

## Initialization

The REPL must be explicitly initialized before any `lean_repl` call:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target" })
```

`lean_repl_import` only works when the REPL is uninitialized, the old process
has been killed, or the live REPL already runs exactly this import block. It
refuses only on a live REPL whose import block differs (killing requires
`bash`, which only the main agent has). It is idempotent: re-sending
exactly the live REPL's current import block succeeds as a no-op and reports
`status: "already-running"`. This matters after a build-restart cycle: an
automatic restart on request reuses the last configured import block, so the
new root may already be live when the main agent's own `lean_repl_import`
arrives — with the same block this succeeds, with a different block it refuses.

The default import block should include:

1. `import Mathlib` — always
2. The current project target file (e.g. `import Target`) — so subagents have
   access to all target-local declarations without pasting them into branches
3. Any Extlib dependencies referenced by the formalization task

The root environment is verified by readiness probes after every spawn; if
any imported module lacks a built `.olean` the import fails loudly naming the
cause — run `cd lean && lake build` for the missing modules and call
`lean_repl_import` again. Failed imports are silent in the repl protocol, so
a `loaded: true` from `lean_repl_status` is the only trustworthy readiness
signal; `initialized: true` alone is not.

Example for a session working on `Target.lean` that references Milne 2021:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target\nimport Extlib.GroupTheory.Mil21" })
```

## Changing imports (restart)

When the target file changes or new Extlib dependencies are needed:

1. `lean_repl_status` → note `pid`
2. `bash kill -TERM -- -<pid>`
3. `lean_repl_import({ imports: "<new import block>" })`

Only the main agent can do this: killing requires `bash`, and
`lean_repl_import` refuses on a live REPL with a different import block.
If a queued worker request auto-restarted the REPL between steps 2 and 3,
the restart reuses the last configured block; step 3 with the new block is
then a genuine (refused-then-retry) import change, while re-sending the old
block is the idempotent no-op.

## One generation per project (conflict guard)

A loaded environment holds ~7.6 GB; two on one host cause OOM kills. Only one
REPL generation per project is therefore supported. Before every spawn
(`lean_repl_import` and automatic recovery) the service scans for REPL
processes of other sessions in the project directory and refuses loudly with
`REPL-CONFLICT` (naming the process group, its RSS, and the exact `kill -9 --
-<pid>` remedy) instead of silently duplicating. This also catches leaked
orphan REPLs from crashed sessions. In-process subagent sessions (workers,
auditor) share the main session's registry and never trigger the guard; it
only fires for a second independent pi process in the project.

## Restart accounting

`lean_repl_status` reports `restartCount` (total), a per-reason breakdown
`restarts` (`crash` — respawn after process death; `timeout` — respawn after a
request exceeded its time limit and the process was killed; `import` — respawn
via `lean_repl_import`), and the last 10 events in `recentRestarts` (reason,
timestamp, from/to generation). `crash`/`timeout` clusters point at toolchain
or payload problems (e.g. OOM); they are not caused by workers, which cannot
kill or re-import the service. Every response also carries `repl` and
`generation` — a change between consecutive responses makes a respawn
detectable from the response alone.

## Build/REPL memory discipline (added 2026-09-19 after 8 OOM crash-respawns)

A loaded REPL holds ~7.4 GB RSS; `lake build Target` re-elaborates the full
target file (multi-GB transient). Together they exceed a 9.9 GB host, and the
kernel kills the REPL — destroying every live worker branch (see
BUILDER_FEEDBACK_OOM_CRASHES.md). Main-agent rules:

- Never run `lake build` while workers hold live branches. Check
  `lean_repl_status`/worker states first; sequence builds between waves.
- Batch integration appends; build once per wave, not per block.
- During a wave, watch `restarts.crash` — if crashes cluster, reduce
  concurrency (the crash family is memory pressure, not worker error).
- `lean_repl_status` now detects concurrent heavy builds itself: a
  `heavyBuildProcesses` field lists `lake`/`lean` processes working in `lean/`
  outside the REPL's process group (heaviest first, with pid, RSS, cmdline),
  and a warning appears once their combined RSS exceeds ~1 GB. The REPL's own
  `lake env` wrapper and REPL binary are excluded (same process group). Use
  this as the build/REPL coexistence check before deciding to build.

## Monitoring

`lean_repl_status` and each response's `health` field report queue age,
restarts, RSS, unexpected process groups, whether the REPL has been
initialized, and whether the root environment is `loaded` (readiness probes
passed). Check before parallel Lean work and after timeouts or unexplained
latency.

A healthy running service has one two-process group (`lake env` plus REPL),
`initialized: true`, `loaded: true`, and no warnings. A `REPL-DOWN` warning
means workers are blocked: the service is dead and could not (or may not)
auto-recover. Diagnose from `lastInitError` / `consecutiveInitFailures`, fix
the cause (usually a missing `.olean` after a rebuild: run
`cd lean && lake build`), then call `lean_repl_import` — this resets the
automatic-recovery failure counter. Workers cannot do any of this; expect
their reports to carry `REPL-DOWN` errors when the window was long.

## Builds

Persistent target files must receive a final project build:

```text
cd lean && lake build Target
```

If an integrated build fails, reproduce the failing fragment in `lean_repl`,
fix it there, and only then rebuild.

The all-`Mathlib` REPL root hides missing target imports: a declaration that
elaborates in the REPL may fail `lake build` with `Unknown constant` when the
target file does not actually import that module. Confirm any library API used
in a target edit is in the target's import closure (via the build, not the
REPL), and add the import when it is not.

After rebuild the REPL must be restarted to include target modifications.

NEVER use tmp lean files to build, always the Target or use the REPL.
