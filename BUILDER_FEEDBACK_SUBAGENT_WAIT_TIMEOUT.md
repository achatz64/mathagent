# Builder request: subagent wait with timeout (checkpoint strategy)

Reported by: main formalization agent (FT session, 2026-09-20)

## Issue

`subagent_wait` and `subagent_wait_any` block until a watched worker completes; there is
no timeout parameter. Main agents therefore cannot implement timed checkpoints ("wake me
after 15 minutes to check REPL health / worker progress / crash counts"). Observed twice
this session: main ends its turn intending a timed checkpoint, control returns to the
user instead, and the checkpoint only happens if the user prompts again. In one window
this cost a 5-crash cluster (12:46–13:24) going unnoticed for ~40 minutes while a single
worker thrashed in oversized REPL calls.

## Goal

A wait-with-timeout surface so main can run autonomous checkpoint loops:

1. `subagent_wait_any(ids, timeout_seconds?)` / `subagent_wait(id, timeout_seconds?)`
   return either the (first) completion, as today, or a timeout marker, e.g.
   `{ "type": "timeout", "watched": [...], "elapsedSeconds": 900 }`, without erroring.
2. On timeout, all watched workers stay live and untouched (no implicit abort/collect);
   the caller re-issues the wait afterwards. Idempotent, no side effects.
3. Optional but useful: the timeout result includes a compact health snapshot
   (worker states + shared REPL restarts counters) so a checkpoint costs one call.

Non-goal: changing completion delivery semantics; the existing "delivered exactly once"
rule must be preserved.

## Context

- Main-agent checkpoint policy (ratified by user 2026-09-20): 15-minute status/crash
  checkpoints, 10-minute emission pings for silent workers, and the 30-minute rule
  (a worker exceeding 30 minutes means the task split was wrong → demand handover
  design, end the worker, redistribute across free slots). All three need a timed wake-up
  to be executable without user intervention.
- Until delivered, main approximates checkpoints at user-turn boundaries; this is
  unreliable and pulls the user into the loop.
