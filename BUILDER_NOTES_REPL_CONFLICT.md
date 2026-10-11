# Builder record — issue E (duplicate REPL generations across concurrent sessions)

Reported in BUILDER_FEEDBACK_REPL_SESSION_STATE.md addendum (commit 5881da1,
marked OPEN/BLOCKING). Resolved 2026-09-19 with the refusal-guard option (b)
per user ratification; option (a) (attach-to-existing) was rejected because a
spawned repl's stdio are pipes owned by its parent process — true cross-process
attach would require a socket-broker redesign, whose only benefit (parallel
testing) is unnecessary given that only builder tests, and builder works with
main closed.

## Premise correction (auditor)

The feared "main launches auditor → auditor spins up repl → duplicate" cannot
happen: `audit_launch` runs the auditor via `createAgentSession` in-process
(like workers), its tool list is `read/grep/bash/edit` — no `lean_repl`
tools — and `AUDIT.md` is build-only. No auditor-specific step needed; the
"kill repl before audit_launch" documentation step is unnecessary.

## What was implemented (option b)

- `foreignReplGroups()` scan (reuses /proc; matches the repl binary by cmdline
  substring `.lake/packages/repl/.lake/build/bin/repl` under the project cwd —
  absolute and relative path forms both match) — used by:
  - `spawnAndInit()`: before ANY spawn (import, auto-recovery), if a foreign
    generation exists → loud `REPL-CONFLICT` error naming group, pids, RSS,
    and the `kill -9 -- -<pid>` remedy. Not counted as a spawn failure
    (the failure cap is unaffected).
  - `entryStatus()`: actionable warning "foreign REPL generation(s) in this
    project: group G (~N MB) — spawns are refused (REPL-CONFLICT); use that
    session or free one with 'kill -9 -- -<pid>'" (replaces the unactionable
    "unexpected project REPL process groups" text; the numeric field remains).
- Grace window: our own just-closed/dying generations (`closedPids`, 20 s) are
  excused, so teardown races and normal recovery never self-refuse.
- Worker guidance (`index.ts` promptGuidelines, subagent protocol): a failure
  starting with `REPL-DOWN` or `REPL-CONFLICT` needs the main agent; stop
  retrying, report as infrastructure blocker.
- Docs: `LEAN_REPL_MAIN.md` ("One generation per project (conflict guard)"),
  `LEAN_REPL_GENERAL.md` (singleton policy note).

## Verification

- `conflict` scenario: foreign repl (relative-path cmdline — the harder case,
  which also exposed and fixed the fragile absolute-path matcher) → status
  warning fires, import refused with REPL-CONFLICT + kill remedy, import
  succeeds after the foreign generation is freed, warning clears.
- Full regression: healthy(6)/sessionstate(12)/recovery(6)/stale(2)/
  already(2)/cap(5)/conflict(5) PASS, zero FAILs.
- Fresh `pi -p` end-to-end: foreign repl → import refused with verbatim
  REPL-CONFLICT (correctly listing two foreign groups when lake/elshim split
  groups), status warning verbatim, warning clears after the kill.

## Addendum (2026-10-11, main): orphan path — non-graceful supervisor death blocks its own session

New incident shape observed with worker w31: the worker **killed its own
generation's supervisor** (attempting a deliberate clean respawn after tainted
session names had accumulated). The supervisor died, but the loaded child
repl process (pid 27004, ~7.1 GB RSS) survived as an orphan and kept holding
the project's single-generation slot. From that point every respawn attempt —
including the worker's own — was refused with `REPL-CONFLICT` naming the
orphan group, and the worker had no tool to free it (workers have no bash).
The session was unrecoverable for the worker; recovery required the main
agent (`kill -9 -- -<pid>`, after which the next respawn succeeded).

Assessment: the guard behaved as designed (one loaded generation per project;
a live pid is a live generation, whatever killed its supervisor), but the
grace window (`closedPids`, 20 s) only excuses graceful closes — an orphaned
child after a SIGKILL'd supervisor is invisible to it. Recording two options
for the builder, both low priority:

1. detect supervisor-less children (ppid 1 / no matching supervisor in the
   process group) in `foreignReplGroups()` and either excuse or auto-reap
   them (they hold ~7 GB each);
2. include the orphan-kill remedy text in the REPL-CONFLICT message even when
   the refused group is the requester's own generation (currently the message
   reads as if the session were foreign, which misled the worker into
   reporting a blocker it could not act on).

Interim worker guidance already in SUBAGENTS.md: a REPL-CONFLICT/REPL-DOWN is
a stop-and-report for workers; the main agent owns kill/respawn.
