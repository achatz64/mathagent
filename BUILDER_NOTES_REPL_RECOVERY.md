# Builder record — BUILDER_FEEDBACK_REPL_RECOVERY.md (resolved 2026-09-18)

## Root causes found (empirically verified against the repl binary, v4.31.0)

1. **Worker starvation after a crash** (`request()` only auto-restarted when a
   request *failed* on an existing repl; a missing/dead entry threw the generic
   "REPL not initialized" error workers cannot act on).
2. **Empty-environment state**: the repl binary reports *failed imports
   completely silently* (no `messages`, no stderr; env counter advances
   regardless). `rootEnvironment()` accepted any numeric env as success, so a
   spawn whose import block failed (typically `Target` without a built
   `.olean` after a rebuild cycle) was reported `initialized` with an empty,
   partly corrupted environment. Verified: failed `import Target` (olean
   missing) → silent success, empty env, and subsequent multi-line commands
   mis-parse ("expected token"); `lake env lean` itself is healthy.
3. **Failed-init left a wedged session** that later requests reused.

## Fixes (all in `.pi/extensions/lean-repl/`)

`service.ts`:
- `rootEnvironment()` now verifies the root: `#check @Lean.Elab...`
  availability probe (strict) + a moduleNames probe checking every module of
  the import block against `env.header.moduleNames` (throws `IMPORT-MISSING:
 <names>`). Root-init timeout 600s (Mathlib load); probe timeout 120s.
- `request()` auto-recovery: dead/missing repl + configured imports →
  respawn + verified root, request proceeds (handle-free) or throws the
  familiar retry-from-new-root notice (stale handles). Missing imports →
  loud `REPL-DOWN: ... lean_repl_import first (main agent only)`.
- Spawn-failure cap: 3 consecutive init failures pause auto-recovery with a
  fast `REPL-DOWN`; `lean_repl_import` resets the counter.
- `initImports` failures close the process, set honest status, keep imports.
- `release()` keeps the registry entry (with imports) so later requests can
  self-recover; entry never deleted mid-flight again.
- Status: `loaded` (probe-verified), `downSince`, `consecutiveInitFailures`,
  `lastInitError`, `initialized` = alive repl; `REPL-DOWN ... workers
  blocked` warning when down. `restartCount` also counts auto-recoveries.

`index.ts`: descriptions updated (readiness probe, auto-recovery, REPL-DOWN);
worker promptGuidelines say to report `REPL-DOWN` as an infrastructure
blocker. `.pi/extensions/subagents/index.ts`: same instruction added to the
lean worker protocol.

Docs: `LEAN_REPL_GENERAL.md` (Default imports section now matches behavior),
`LEAN_REPL_MAIN.md` (readiness signal, healthy-service criteria, recovery
procedure).

## Verification

- Probe syntax validated in plain `lake env lean` and in the repl (pass case,
  `IMPORT-MISSING` case, exact generated string).
- Direct service tests (`/tmp/test_service.mjs`): healthy init, broken block
  (missing Target.olean → loud readiness error, honest status), SIGKILL
  recovery (new pid, loaded root, restartCount 1), idempotent re-import,
  stale-handle rejection, failure cap (fast fail), no-init REPL-DOWN.
- Fresh `pi -p` end-to-end (TESTING.md): import → check → status (healthy,
  loaded, 7.5GB RSS); kill process group → request auto-recovers with
  verified root; broken import fails loudly with actionable error.

## Notes for main

- Until `Target` is rebuilt, `import Target` in the block will fail loudly —
  run `cd lean && lake build` first (readiness probe catches it; previously
  this produced the silent empty-environment state).
- `loaded: true` is the trustworthy readiness signal; `initialized: true`
  alone is not (dead process now reports initialized: false, but during the
  init window it is alive-not-yet-loaded).
