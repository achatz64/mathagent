# Lean REPL

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

## Default imports

The REPL's imports include the current project target file, Mathlib, and any
Extlib dependencies set by the main agent. Call `lean_repl_status` to inspect
the active `imports` block, whether the REPL is `initialized`, and whether the
root environment is `loaded` (verified by readiness probes). Use
target-local declarations directly without pasting them into branches.

`loaded: true` is only reported after the root environment passed readiness
probes: the repl binary silently swallows failed imports (no error messages,
environment counter still advances), so the service re-checks after every
spawn that the environment can elaborate and that every module of the import
block actually loaded. If a module lacks a built `.olean` (e.g. the target was
cleaned by a rebuild), initialization fails loudly instead of delivering an
empty environment.

If the REPL dies (e.g. after a timeout), it restarts automatically on the next
request, reusing the last import block configured via `lean_repl_import`. This
also works from worker sessions: a failed request spawns the service again and
reports the restart; retry from the new root without stale `env`/`repl`
values. A failure whose message starts with `REPL-DOWN` means automatic
recovery itself failed — stop retrying and report it as an infrastructure
blocker; only the main agent can fix it (rebuild missing modules, then call
`lean_repl_import`). A main agent that just killed the REPL to change imports
may therefore see the new root appear before its own `lean_repl_import` call
arrives; with an unchanged import block the call is an idempotent no-op
(`status: "already-running"`), with a changed block it refuses. Check the
`imports` field of the response rather than assuming the call order.

After 3 consecutive failed initializations the service pauses automatic
recovery and fails fast with `REPL-DOWN` until the main agent calls
`lean_repl_import` again (which resets the counter).

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`.
