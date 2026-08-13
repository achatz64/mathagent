# Lean REPL

Pi loads `.pi/extensions/lean-repl/` by default. The extension maintains one
project-wide Lean REPL shared by the main SDK session and managed subagents.
It starts the compiled REPL through `lake env` and serializes all requests
through a FIFO queue.

## Initialization

The REPL must be explicitly initialized before any `lean_repl` call:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target" })
```

`lean_repl_import` only works when the REPL is uninitialized or the old process
has been killed. Call it once at session start.

The default import block should include:

1. `import Mathlib` — always
2. The current project target file (e.g. `import GT`) — so subagents have
   access to all target-local declarations without pasting them into branches
3. Any Extlib dependencies referenced by the formalization task

Example for a session working on `Target.lean` that references Milne 2021:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target\nimport Extlib.GroupTheory.Mil21" })
```

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
Omitting `env` starts from the shared root.

Do not send `import` commands through `lean_repl`: later REPL calls elaborate
inside an existing environment, not at the beginning of a Lean file. Never use
broad `#find` in the shared process. Search checked-out Mathlib source narrowly,
then verify exact names with `#check`, `#print`, or `#synth`.

Always retain and pass `repl` together with an `env` that crosses turns or is
handed to another agent. Bare integer environments remain accepted for
compatibility, but cannot detect that the REPL has restarted. A stale
`repl` token is rejected instead of accidentally addressing an unrelated
environment number.

## Changing imports (restart)

Only the main agent can restart the REPL:

1. `lean_repl_status` → note the `pid`
2. `bash kill -TERM -- -<pid>`
3. `lean_repl_import({ imports: "<new block>" })`

Subagents cannot call `lean_repl_import` on a live REPL — it refuses if the
process is alive. Killing requires `bash`, which only the main agent has.

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`.