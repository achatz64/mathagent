Before working in this repository, read `OVERVIEW.md`. It is the source of
truth for the project's vision, architecture, and rules.

# MPC instructions

## `lean-explore` searches

For every `lean-explore` `search` or `search_summary` call, pass
`rerank_top` explicitly and use `0` by default. Never omit it.

Treat `lean-explore` result IDs as local to the current index and session. Do not report them to user.

## Lean execution

Pi loads the project-local Lean REPL extension by default. See [LEAN_REPL.md](LEAN_REPL.md). Use this repl and DO NOT build tmp files to be compiled with `lake build`. The repl is much faster! Of course, the target output files have to be checked with `cd lean && lake build ...`.


