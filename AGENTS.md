Before working in this repository, read `OVERVIEW.md`. It is the source of
truth for the project's vision, architecture, and rules.

# MPC instructions

## `lean-explore` searches

For every `lean-explore` `search` or `search_summary` call, pass
`rerank_top` explicitly and use `0` by default. Never omit it.

Treat `lean-explore` result IDs as local to the current index and session. Do not report them to user.

## Lean execution

Pi loads the project-local Lean REPL extension by default. Read and follow
[LEAN_REPL.md](LEAN_REPL.md). Use this REPL and DO NOT build temporary files with
`lake build`. Target files still require a final `cd lean && lake build ...`.
If that build fails, isolate and fix the problematic code in the REPL before
building again. Treat large target builds as monitored stress tests: check REPL
and OS process/memory state first, time the build with peak RSS when diagnosing
regressions, and compare against the last known-good target. Do not raise
`maxHeartbeats` to force an unverified proof through; restore the known-good
file if an integrated block causes kernel timeouts or a major time/RSS
regression, then repair the block in isolation.

## Managed proof workers

Before delegating work, read and follow [SUBAGENTS.md](SUBAGENTS.md). In
particular, Lean workers are read-only, receive the complete source statement
and proof, and return proof fragments for main-agent review and integration.
Use event-driven subagent tools rather than Bash polling. The main agent remains
responsible for semantic review, integration, validation, and commits.


