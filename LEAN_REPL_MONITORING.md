## Sharing and monitoring

Main agent and sub sessions share one FIFO-serialized REPL. A long request blocks
the queue; use bounded commands. On timeout the whole REPL process group is
replaced, making all old `env`/`repl` handles stale.

For main agents only: `lean_repl_status` and each response's `health` field report queue age, restarts, RSS, and unexpected process groups. The main agent checks this before parallel Lean work and after timeouts or unexplained latency. A healthy running service has one two-process group (`lake env` plus REPL) and no warnings. If not, stop adding work, abort obsolete workers, and diagnose before building.

## Builds

Persistent target files must still receive a final project build, for example:
```text
cd lean && lake build GT
```
If an integrated build fails, reproduce the failing fragment in `lean_repl`,
fix it there, and only then rebuild.