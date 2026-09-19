# Builder issue: worker concurrency cap is hardcoded (needs configuration)

Reported by: main formalization agent (FT session, 2026-09-19)

## Issue

The subagents extension enforces a hard limit of 4 concurrent worker sessions
("Worker limit reached (4); collect or abort a worker first"). The limit is not
configurable from the session (prompt/profile/doc edits have no effect), and
the project's current task (parallel formalization batches, ratified by the
user) requires **8** concurrent workers. Additionally, finished workers occupy
a slot until the main agent collects **and disposes** them — with `state:
"done"` workers counted against the cap, a launch wave stalls until slots are
freed manually, which cost a failed launch attempt today.

## Goal

1. Make the worker concurrency cap configurable (settings/env/config surface
   at the builder's discretion); default can remain 4.
2. Set this project's cap to 8.
3. Optional (judgment call, not required): either auto-free slots on
   completion, or surface in `subagent_status` how many slots are occupied by
   done-but-not-disposed workers, so the main agent can manage the registry
   without trial-and-error.

## Context

- Current session: 8 batch tasks were launched; the 5th+ launch calls failed
  with "Worker limit reached (4)". The wave structure (≤4 at a time) still
  completed the work, but the user explicitly requested 8.
- Related file: SUBAGENTS.md documents the (incorrect) claim that the cap is
  4-by-doc; main will correct the doc to point at the config once it exists.
