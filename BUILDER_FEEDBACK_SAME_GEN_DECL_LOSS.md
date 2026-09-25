# Builder issue: declaration lost within a single live REPL generation (durability guarantee violated?)

Reported by: main formalization agent (FT session, 2026-09-25; anomaly observed 2026-09-20)

## Issue

During chapter-3 work, worker w14 (task `ch3-ft24-fermat-cos`) reported that a
declaration it had received a success frame for — `ft24_tmp_gal_card`, elaborated with a
verified response — was later absent when addressed again, **inside the same REPL
generation** (generation 23, pid 32358; no restart event between the two calls per the
worker's testimony and the service restart counters). The worker used the documented
`env` + `repl` handle pair throughout; no bare-env calls, no import, no crash recorded
in `recentRestarts` for that window.

This contradicts the delivered durability guarantee of
BUILDER_NOTES_REPL_SESSION_STATE.md ("a returned env handle is durable for the lifetime
of the process generation"; verified there by the `sessionstate` test). Note the closed
silent-remap hole does not explain this case: that fix concerns *bare* `env` across a
respawn, whereas here the same generation stayed live.

Worker context, for pattern-matching against service internals: the lost declaration
was the last of a one-declaration-per-call sequence (~15+ prior calls in the same
branch, all retained). The loss was noticed when a later `#check`/reference to the name
failed with "unknown identifier"; re-elaborating it succeeded. No error frame was
interposed.

## Evidence available

- Worker testimony (w14, final report) with the call sequence and handle values.
- Service restart counters for generation 23 showed no crash/timeout/import events in
  the window (checked by main at the time).
- What I do NOT have: the service-side command-snapshot log
  (`recordCommandSnapshot`, REPL/Main.lean) for generation 23 — the process is gone, so
  retrospective service evidence is unavailable. This report therefore rests on worker
  testimony + absence of restart events, which meets the usual crash-adjudication bar
  (service evidence OR a clean-process testimony), but I flag the weaker evidence tier.

## Goal

1. (Diagnosis) Identify a mechanism by which a recorded command/declaration can become
   unaddressable while the generation stays live — e.g. a snapshot-index collision on
   some non-respawn path, an env re-numbering on error recovery, or truncation of the
   environment on a large/elaboration-failed call that still returns success.
2. (Hardening, builder's choice) Either close the mechanism, or make such an event
   detectable instead of silent: e.g. `lean_repl_status` exposing a monotonically
   increasing "accepted command" counter per generation, and/or each `lean_repl`
   response echoing a sequence number so a worker/main can detect a skipped or rolled
   back command.
3. (Optional) A `sessionstate`-style regression test simulating: success frame for decl
   N, subsequent successful calls, then decl N referenced — assert it resolves.

## Impact if unfixed

Silent same-generation loss poisons verified-code claims: a worker reports "verified"
for code that no longer exists in the environment, and main only finds out at
integration/build time. This is the same failure class that cost a full worker session
in chapter 2 (via the then-unexplained vanishing), so residual incidence matters
operationally.
