# Builder record — BUILDER_FEEDBACK_STALE_OLEAN_RESPAWN.md (fix delivered 2026-10-10)

Both requested remedy levels delivered (1 and 2 of the feedback; remedy 3's
minimal timestamp echo is subsumed — the no-op response now also changes
status instead of staying byte-identical).

## Verified mechanism (implementation-checked)

1. `service.ts` `request()`: any requester auto-respawns a dead service with
   the last configured import block. During a `kill → lake build` window, such
   a respawn loads the pre-rebuild olean.
2. `initializeRoot()` probes check only Lean availability and module-name
   presence in `env.header.moduleNames` — a stale (pre-rebuild) olean passes
   both; nothing checked currency.
3. `initImports()`: unchanged import block + alive repl → `"already-running"`
   with no re-elaboration, and no response/status field could distinguish the
   stale root from a fresh one.

## Key design insight: spawn time, not load completion

The repl reads each module's `.olean` once, at that module's position in the
import sequence. A build finishing during a root load can therefore leave the
root stale even though the load (and probes) completed later. The staleness
base is the **spawn moment** of the generation (`rootSpawnedAt`), recorded in
`spawnAndInit` before `new SharedRepl(...)`. Consequences:

- True positive (root read old olean, build wrote later): detected, repaired.
- False positive (build finished before the repl's read of that olean): root
  is actually fresh but flagged — conservative direction, costs one harmless
  extra respawn. The regression harness initially "failed" because it assumed
  the impossible ordering (fast build finishing before a slow `import Lean`
  completed, then expecting the old decl) — the repl had legitimately read the
  fresh olean. See regression notes below.

## The fix (`.pi/extensions/lean-repl/service.ts`, `index.ts`)

- After the readiness probes pass, one extra probe asks the live root — via
  `Lean.findOLean` (verified available in v4.31.0; elaboration tested in
  `lake env lean` and through the repl binary) — where each import-block
  module's `.olean` lives. Paths come from the environment's own search path
  (LEAN_PATH), so no lake-layout guessing. Result stored as
  `entry.importOLeanPaths`; any probe failure degrades silently (feature off,
  init unaffected).
- `staleImportModules(entry)`: sync stat of the recorded paths; module is
  stale iff `statSync(path).mtimeMs > rootSpawnedAt`. Missing file (clean /
  rebuild in progress) is not a staleness signal — a missing olean fails the
  presence probes loudly on the next spawn.
- `initImports()` unchanged-block branch: no-op only when
  `staleImportModules()` is empty. Otherwise: close live generation, respawn
  with the same block (recorded as a normal `import` restart), return
  `"initialized-stale-reload"`. Failure cap bypassed (`ignoreCap`) — this is a
  main-agent-initiated deliberate reload.
- `entryStatus()`: new fields `rootSpawnedSince` (ISO) and `staleRootModules`,
  plus warning "stale root: rebuilt .olean(s) of … postdate the loaded root —
  call lean_repl_import with the same import block to re-elaborate". Covers
  the never-re-imports case (remedy 2).
- `lean_repl_import` tool description documents `"initialized-stale-reload"`.

## Interim main-agent discipline (from the feedback) — still in force

The spot-check `#check` of a new-only declaration remains the primary
verification; staleness fields are a safety net (and can flag conservatively).
Undeterminable degradation reports empty `staleRootModules` silently.

## Known limitations (accepted)

- Only import-block modules are tracked. A rebuilt *transitive* dependency
  (e.g. an Extlib chapter imported by Target but not by the import block)
  that leaves Target.olean itself untouched is not detected. The dominant
  workflow (edit Target.lean → `lake build Target`, block includes Target)
  is covered; the presence probes have the same scope.
- Conservative false positives possible in the late-read ordering (above).

## Verification

- `tsc --noEmit --strict` over service.ts: error set identical to baseline
  (2 × TS2769 spawn stdio readonly). index.ts changed only a description
  string.
- Regression `tmp/regression_stale.mjs` (node --experimental-strip-types;
  lightweight scratch module `Extlib.ScratchStaleTest` in the `Extlib.+` glob
  instead of Mathlib/Target, ~3 min total):
  - 6 unit cases for `staleImportModules` (fresh / stale / missing / degraded
    / dead / not-loaded).
  - Integration: fresh import → initialized; unchanged block on fresh root →
    already-running (no-op intact); bug reproduction (kill → respawn on old
    olean → rebuild → status flags `["Extlib.ScratchStaleTest"]` + warning →
    unchanged-block import → `initialized-stale-reload`, new generation,
    fresh status, new decl `#check` passes) → no-op again on reloaded root;
    changed-block loud refusal preserved. ALL PASS (22/22).
- Fresh `pi -p` end-to-end: import Lean → initialized; re-import →
  already-running; status exposes `rootSpawnedSince`, `staleRootModules: []`,
  no stale-root warning. Tool-layer wiring verified.
- Harness cleans up its scratch module and build artifacts; no leftover repl
  processes after runs (lease released, singleton guard respected).

## Note

`tmp/GT_EXPLORATION.md` was already deleted in the working tree before this
builder session started (unrelated to this fix; flagged for main to confirm
intentional).