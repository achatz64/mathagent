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

Always pass `repl` together with an `env` that crosses turns or is handed to
another agent. A bare `env` (without `repl`) is only accepted when it equals
the current root environment; anything else is refused loudly instead of
silently remapping onto an unrelated snapshot after a respawn. A stale `repl`
token is rejected instead of accidentally addressing an unrelated environment
number.

## Session state

The shared environment is disposable by design. The only durable state is the
import block; all scratch state (env handles, elaborated declarations) may be
destroyed at any time by a respawn — after a crash, a timeout, or recovery.
Never depend on the shared environment surviving a respawn: emit completed
work as code text (or a file/commit), or keep it re-derivable by
re-elaborating from the root.

Within one process generation, a returned `env` handle is durable: the repl
records a command's snapshot before answering, so a successful response
means the environment survives later calls in the same generation. A
declaration batch can only vanish together with the whole generation —
detectable via the response's `repl`/`generation` fields (and `restartCount`
in `lean_repl_status`). If those changed since your previous call, the
environment was reset: re-elaborate what you need from the root.

Keep single calls moderate (roughly up to a few hundred lines). Very large
blocks are slower to retry, can exceed the per-call timeout (which restarts
the process, loudly), and on a memory-loaded machine (~7.6 GB RSS for a
loaded environment on a 9 GB host) plausibly risk the process being killed.
Prefer several sequential batches with a persistence spot-check (`#check` of
a fresh declaration) between them.

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

Only one loaded REPL generation per project is supported (~7.6 GB each; two
on one host cause OOM kills). A second independent pi process in the project
is refused with `REPL-CONFLICT` (naming the foreign process group and the
`kill -9 -- -<pid>` remedy) instead of spawning a duplicate; in-process
subagent sessions share the main session's generation and are unaffected.

## Development and builds

Use the REPL for proof development and API checks. Do not create temporary Lean
files merely to invoke `lake build`.

## Environment resets are collective and unannounced (design policy)

The only durable state of the shared REPL is the import block. All session
scratch state — env handles and in-flight declarations — is disposable by
design: the service may respawn at any time (after a crash, a timeout, or as
part of recovery) without asking sessions, and a respawn resets the
environment for every session, not just the one that triggered it.

Therefore, as a worker or the main agent:

- Never depend on the shared environment surviving a respawn. Work that
  matters must be emitted (returned as code text, written to a file, or
  committed) or be re-derivable from the root by re-elaboration.
- On a respawn (stale handles, generation change), simply retry from the
  root: omit the `env` handle; the fresh branch from the configured import
  block is clean. Failed declarations pollute only your branch — dropping
  the handle is the cleanup, not a service restart.
- Never deliberately restart or kill the shared service to clean scratch
  state; that resets every other session.
- A failure whose message starts with `REPL-DOWN` means recovery itself
  failed; report it as an infrastructure blocker (main agent fixes).
