# Lean REPL

The project-wide shared Lean REPL is initialized by the main agent before any
`lean_repl` call. Do not attempt to initialize or restart it.

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

## Target-local declarations

The root imports include the current project target file. Use its declarations
directly without pasting them into branches.

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`.