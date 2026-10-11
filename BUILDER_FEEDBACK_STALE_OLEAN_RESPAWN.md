# Builder issue: stale-olean window after kill/build — undetectable via `lean_repl_import`

**Status:** open (2026-10-10, main)
**Component:** `.pi/extensions/lean-repl/` (service.ts: dead-service recovery +
`lean_repl_import` no-op path)

## Verified mechanism (implementation-checked, not doc-inferred)

1. `service.ts` (dead-service recovery, ~lines 697–714): **any requester,
   including read-only workers, auto-respawns a dead service** with the last
   configured import block:
   ```ts
   if (!current || !current.alive) {
     // Crash/dead service recovery: any requester (including read-only
     // workers, which cannot call lean_repl_import) re-spawns the REPL with
     // the last configured import block.
     current = await spawnAndInit("crash");
   ```
   Workers therefore *trigger* automatic respawns (their plain `lean_repl`
   calls suffice); they cannot initiate them deliberately. SUBAGENTS.md's
   phrase "not caused by workers, which cannot kill or re-import the service"
   is true as stated but easy to misread — worth a clarifying word ("cannot
   deliberately kill or re-import; their requests may trigger the automatic
   recovery path").

2. Main-agent import-change flow (LEAN_REPL_MAIN.md): `kill -TERM -- -<pid>` →
   `lake build Target` (multi-GB, minutes) → `lean_repl_import` with an
   **unchanged** import block.

## The bug

During the build window of step 2, any queued worker `lean_repl` request
auto-respawns the service (crash-recovery path above) and loads whatever
`Target.olean` exists at spawn time — the **stale pre-rebuild one** (a stale
olean passes the readiness probes; they only check that modules load, not that
they are current). Afterwards the main agent's `lean_repl_import` with the
same, unchanged block hits the idempotent no-op path
(`status: "already-running"`) and does not re-elaborate the fresh olean.

Result: the shared root silently keeps stale target-local declarations, and
**no response field can distinguish it** — `imports`, `initialized`,
`loaded`, `generation`, `restartCount` are all identical to the healthy case.
The `imports` field remedy suggested in LEAN_REPL_GENERAL.md cannot detect
this, because only the olean differs, not the block. Worker results verified
against stale target declarations then fail (or worse, silently mismatch)
after the next genuine respawn.

Note: the changed-block half of this race is already analyzed in
LEAN_REPL_MAIN.md ("If a queued worker request auto-restarted the REPL between
steps 2 and 3 …"); the unchanged-block half is not, and has no detection story.

## Requested remedy (sketch, non-binding)

Any of these suffices:

1. `lean_repl_import` with an unchanged block: if a no-op, verify the live
   root's spawn/load timestamp postdates the newest `.olean` mtime of the
   imported modules; if not, re-run the root load (or say so loudly).
2. Surface the root's spawn timestamp + the mtimes (or a hash) of each
   imported module's `.olean` in `lean_repl_status` (`staleness` field), so
   the main agent can check before integrating after a rebuild.
3. Shortest workaround-level fix: make the no-op response carry the spawn
   timestamp so the main agent can compare it against the build finish time.

## Interim main-agent discipline (applied until fixed)

After `kill → build`, never accept `already-running` as "fresh root":
spot-check `#check` of a declaration that exists only in the *new* target
version; on the old version it fails (or has a different type). If the check
passes against the stale olean, force a genuine respawn (kill again →
`lean_repl_import`).

See also: BUILDER_FEEDBACK_OOM_CRASHES.md (build/REPL memory interplay that
motivates the kill-before-build sequence in the first place).
