# Builder issue — shared REPL crash leaves service down; workers starve with no recovery path

Reported by: main formalization agent (FT/Milne-FT v5.00 session, 2026-09-17,
chapter-1 worker batch `ft-ef31-cyclotomic`, `ft-ef25-26-27-constructible`,
`ft-ef24-linecircle`, `ft-ef28-30-impossible`)
Component: `.pi/extensions/lean-repl/` (service lifecycle + worker recovery)

## Symptom

During a four-worker batch the shared REPL process crashed (observed as
generation `3:17148` disappearing with `lastRestartReason: "Lean REPL is not
running"` after a main-agent kill plus a worker request racing the restart).
Afterwards, every worker `lean_repl` call failed with:

```
REPL not initialized — call lean_repl_import first
```

Workers (profile `lean*`, tools `read/grep/lean_repl` only) cannot run
`lean_repl_import` (correctly main-only), so all three live workers starved:

- `ft-ef31-cyclotomic`: burned its verification budget on 13 failed calls,
  delivered grep-verified-only code (tactic errors found later by main).
- `ft-ef28-30-impossible`: same starvation; delivered code with ~6 distinct
  elaboration failures that main had to repair by hand.
- `ft-ef25-26-27-constructible`: stalled in retry loops until main noticed.

Main only discovered the problem when reviewing the first delivery — the
workers' intermediate progress reports did mention it, but the batch kept
running for ~40 minutes in the degraded state.

## Reproduction

1. Main initializes the REPL (`lean_repl_import`, imports M + Target + Mil21).
2. Spawn ≥1 `lean*` workers using `lean_repl`.
3. Main kills the REPL process group (`kill -TERM -- -<pid>`) as part of a
   rebuild cycle, and a worker request lands in the killed window (or the
   process crashes for any reason).
4. Result observed this session: the service did NOT auto-restart on the
   worker request; it stayed `initialized: false` with `processGroupMembers: 0`
   until main explicitly ran `lean_repl_import` again.

Note the contradiction with the docs: `LEAN_REPL_GENERAL.md` (Default imports
section) states the REPL "restarts automatically on the next request, reusing
the last import block configured via `lean_repl_import`". In this session the
auto-restart did fire once during the *kill→re-import race* (which the Issue-3
fix handles correctly — the idempotent `already-running` path worked as
designed), but after the subsequent crash the service stayed down.

## Impact

- Workers cannot self-recover and have no signal to distinguish "briefly busy"
  from "service down"; they either spin, stall, or deliver unverified code
  with an honest blocker note — all three happened in one batch.
- Main only learns of the starvation from reading worker reports; there is no
  push notification, so the degraded window lasts as long as the main agent's
  attention gap (here ~40 min, with the user away).
- Direct quality cost: unverified worker code required substantial main-agent
  repair (the w2 repair loop took ~10 REPL iterations).

## Suggested fixes (optional, builder's call)

1. Restore crash-auto-recovery: if a `lean_repl` call finds the service dead
   (not merely busy), the extension itself re-spawns it with the last
   configured import block, as the docs already promise.
2. If workers must remain unable to trigger recovery, make the failure
   mode loud and cheap: a distinct, greppable error class (e.g.
   `REPL-DOWN <generation>`) instead of the generic "not initialized", plus a
   main-agent-visible flag in `lean_repl_status`/`subagent_status` warnings
   (e.g. "workers blocked: repl down since T").
3. Align `LEAN_REPL_GENERAL.md` with whichever behavior is implemented
   (currently it promises auto-restart-on-request, which only half-holds).

## Addendum (same session, later): recovery now produces a broken empty environment

After several hours of further use, the failure mode escalated. Reproducible
across **six** recovery attempts (graceful kill + re-import, SIGKILL of the
inner process, process-group kill, `pkill -9`, and two timing variants):

1. `lean_repl_import` spawns the REPL and reports `initialized: true` with the
   configured imports.
2. Immediately after, `lean_repl_status` shows `restartCount: 1` with
   `lastRestartReason: "Lean REPL is not running"` — the freshly spawned REPL
   died and something auto-restarted it.
3. The auto-restarted instance has an **empty Lean environment**: even
   `example : True := trivial` fails with `Unknown identifier 'trivial'` and
   `Unknown constant 'OfNat'` — no core, no Mathlib, no Target — while the
   extension's bookkeeping continues to claim the configured imports.
4. The inner REPL process RSS plateaus at ~2 GB (vs. ~7.5 GB for a loaded
   environment) and never grows: it is wedged mid-initialization or is not
   initializing at all.

Consequence: `lean_repl` is unusable while `lake build` continues to work
fine, so the failure is isolated to the REPL service, not the toolchain.
Also notable: commands sent during the import window appear to wedge the
service (first observed this way), but the empty-environment state persists
even when no command is sent until well after import.

Until fixed, the workaround is to rely on `lake build Target` (authoritative
for type-correctness, linters, and the axiom ledger via the file's declared
axioms) and defer `#print axioms` re-checks to a recovered REPL.  The
`lean_repl_status` `initialized` flag cannot be trusted in this state; a
reliable readiness signal is needed (e.g. status reports `loaded: true` only
after the environment actually answers a probe elaboration).
