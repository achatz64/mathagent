# Builder record — BUILDER_FEEDBACK_SUBAGENT_WAIT_TIMEOUT.md (resolved 2026-09-20)

Delivered both builder-actionable items: the wait-with-timeout surface and the
REPL/build OOM coexistence signal (remedy 2 of BUILDER_FEEDBACK_OOM_CRASHES.md).
All changes are static and take effect at the next extension reload; the live
session keeps the previously loaded modules until then.

## 1. `timeoutSeconds` on `subagent_wait` / `subagent_wait_any` (`.pi/extensions/subagents/index.ts`)

- Optional parameter `timeoutSeconds` (1–3600, fractional values rounded up).
  Omitted = historic blocking behavior, byte-for-byte unchanged.
- On expiry the tool returns a `type: "timeout"` result — no error, no throw:
  - `watched`: ids of the watched workers;
  - `elapsedSeconds`: actual wait time;
  - `workers`: full per-worker snapshots (id, label, state, elapsed,
    currentTool, latestText tail) so a checkpoint can also judge emission
    silence and steering needs;
  - `leanRepl`: full shared-REPL status — restart counters, generation,
    warnings, and (new, see below) `heavyBuildProcesses`. One timed checkpoint
    call therefore covers worker health, crash counters, and build/REPL
    coexistence.
- Side-effect guarantees: on timeout no worker is aborted, collected, disposed,
  or marked `delivered`. Completions remain fresh, so re-issuing the wait (with
  or without a new timeout) returns the completion as usual — the
  "delivered exactly once" rule is untouched. The timer is cleared on every
  exit path; cancellation (signal abort) behaves exactly as before.
- Precedence: an already-completed-but-undelivered worker still returns
  immediately (never waits for the timeout); `wait_any` keeps its
  "no uncollected completions" immediate answer when nothing live remains.
- Out-of-range values (< 1, > 3600, non-finite) fail loudly with a descriptive
  error.

## 2. Concurrent heavy-build detection (`.pi/extensions/lean-repl/service.ts`, OOM remedy 2)

- New `projectHeavyBuildProcesses(projectDir, ownGroup)` scan: lists `lake` and
  `lean` processes whose cwd is the project dir (`lean/`) and whose process
  group is not the resident REPL's. The REPL's own `lake env …/repl` wrapper
  and the REPL binary are excluded via the process-group check — verified
  against the live process tree (wrapper pgid = REPL pgid).
- `lean_repl_status` / subagent responses now carry `heavyBuildProcesses`
  (pid, RSS KiB, truncated cmdline; heaviest first) and emit a warning once
  the combined build RSS exceeds ~1 GB:
  "heavy build process(es) in this project (~N MB RSS) — concurrent builds can
  OOM-kill the REPL; sequence builds between worker waves".
- This is read-only /proc inspection; it spawns nothing and touches no REPL
  lifecycle path.

Remedy status for the OOM feedback: (1) system-level OOM preference — needs
user privileges, not built; (2) detection + warning — delivered; (3) build-side
memory cap — not built (main already sequences builds per wave; the new warning
enforces that discipline at decision time).

## Verification (no REPL use, per constraint; main session was live)

- `tsc --noEmit --strict` (nodenext, strip-friendly flags) over both modified
  files: the error set is identical to the HEAD baseline (2 × TS2769 spawn
  stdio readonly, 3 × TS2339 worker-literal narrowing, 2 × TS1479 module-style
  artifacts of the ad-hoc typecheck setup). Zero new type errors.
- Detector logic exercised at runtime by importing the extracted function with
  Node's type stripping and reading /proc: negative case empty for a foreign
  dir; live `lake env …/repl` wrapper detected only when `ownGroup` does not
  match, correctly excluded when it does; group-filter semantics confirmed.
  No REPL calls, no test pi sessions, no builds, no large allocations.

## Note on param naming

The feedback sketch used `timeout_seconds?`; the delivered parameter is
`timeoutSeconds`, matching the extension's existing camelCase parameters
(`followUp`, `dispose`). Tool descriptions and SUBAGENTS.md document it.
