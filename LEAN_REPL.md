# Lean REPL

Pi loads `.pi/extensions/lean-repl/` by default. The extension maintains one
project-wide Lean REPL shared by the main SDK session and managed subagents.
It starts the compiled REPL through `lake env`, imports `Mathlib` once, and
serializes all requests through a FIFO queue.

## Basic use

Call `lean_repl` with Lean code in `cmd`. The response includes an environment
number, REPL-generation token, and process ID:

```text
lean_repl({ cmd: "def x : Nat := 37" })
-- { ..., env: 1, repl: "1:48211", pid: 48211 }

lean_repl({ cmd: "#check x", env: 1, repl: "1:48211" })
```

Passing an environment continues from it. Reusing an earlier environment
creates a branch; elaboration does not mutate that earlier environment.
Omitting `env` starts from the shared Mathlib root.

The root has already executed `import Mathlib`. Do not send `import` commands
through the tool: later REPL calls elaborate inside an existing environment,
not at the beginning of a Lean file. The persistent project target is not loaded
into the root; paste any required project-local prerequisites into a branch.
Never use broad `#find` commands in the shared process. Search checked-out
Mathlib source narrowly, then verify exact names with `#check`, `#print`, or
`#synth`.

Always retain and pass `repl` together with an `env` that crosses turns or is
handed to another agent. Bare integer environments remain accepted for
compatibility, but cannot detect that the REPL has restarted. A stale
`repl` token is rejected instead of accidentally addressing an unrelated
environment number.

## Sharing and concurrency

Extension instances acquire reference-counted leases on a process-wide service
keyed by the resolved Lean project directory. Consequently:

- the main agent and all in-process managed subagents see the same environments;
- worker shutdown does not terminate a REPL still leased by another session;
- the final lease release terminates the process;
- only the service writes to stdin, so protocol frames cannot interleave.

Lean elaboration itself is serialized. Agents can reason concurrently, but one
long Lean request delays every queued request. Prefer bounded exploratory
commands and branch from known-good environments. A request timeout or framing
failure closes the shared process because continuing would be unsafe; all old
environment handles then become stale.

The PID reported by the tool is the `lake env` owner. The operating system may
also show its actual REPL child; this pair represents one logical shared REPL.

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`. Persistent target files must still receive
a final project build, for example:

```text
cd lean && lake build GT
```

If an integrated build fails, reproduce the failing fragment in `lean_repl`,
fix it there, and only then rebuild.
