# Lean REPL — Main Agent

This file is for the main agent only. Subagents read `LEAN_REPL_GENERAL.md`.

## Initialization

The REPL must be explicitly initialized before any `lean_repl` call:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target" })
```

`lean_repl_import` only works when the REPL is uninitialized or the old process
has been killed. It refuses on a live REPL (kill requires `bash`, which only the
main agent has).

The default import block should include:

1. `import Mathlib` — always
2. The current project target file (e.g. `import GT`) — so subagents have
   access to all target-local declarations without pasting them into branches
3. Any Extlib dependencies referenced by the formalization task

Example for a session working on `Target.lean` that references Milne 2021:

```text
lean_repl_import({ imports: "import Mathlib\nimport Target\nimport Extlib.GroupTheory.Mil21" })
```

## Changing imports (restart)

When the target file changes or new Extlib dependencies are needed:

1. `lean_repl_status` → note `pid`
2. `bash kill -TERM -- -<pid>`
3. `lean_repl_import({ imports: "<new import block>" })`

Only the main agent can do this: killing requires `bash`, and
`lean_repl_import` refuses on a live REPL.

## Monitoring

`lean_repl_status` and each response's `health` field report queue age,
restarts, RSS, unexpected process groups, and whether the REPL has been
initialized. Check before parallel Lean work and after timeouts or unexplained
latency.

A healthy running service has one two-process group (`lake env` plus REPL),
`initialized: true`, and no warnings. If not, stop adding work, abort obsolete
workers, and diagnose before building.

## Builds

Persistent target files must receive a final project build:

```text
cd lean && lake build Target
```

If an integrated build fails, reproduce the failing fragment in `lean_repl`,
fix it there, and only then rebuild.

After rebuild the REPL must be restarted to include target modifications.
