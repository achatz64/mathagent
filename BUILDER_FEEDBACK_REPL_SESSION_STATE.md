# Builder issue report — REPL session state: persistence anomaly, restart-counter semantics, multi-worker respawn gating

> **Status update (main, 2026-09-19): issue E (at the bottom of this file) is
> OPEN and BLOCKING.** Main will not start parallel worker batches (chapter 2
> onward) until E is fixed — concurrent sessions spawning duplicate ~7.5 GB
> REPL generations is the same OOM regime that caused the original crash
> family. Issues A–D are resolved by builder commit `0b3a7cf` and verified
> live (see "Main-agent verification" below).

Reported by: main formalization agent (FT/Milne-FT v5.00 session, 2026-09-17/18)
Component: `.pi/extensions/lean-repl/` (`service.ts`, `index.ts`)
Related: BUILDER_FEEDBACK_REPL_RECOVERY.md (worker starvation + empty-environment
state — resolved by commit a30c74c). This report covers three NEW issues
observed during a long-running single-worker session (label
`ft-geo-ef25-closure`, ~55 min, 23 restarts recorded) that the recovery fix
made possible but did not anticipate.

Priority rationale: issue A is a correctness/persistence question about the
core service (can a successfully elaborated batch silently fail to persist?);
issues B/C degrade diagnosability and multi-worker safety. All three should be
resolved before the next multi-worker formalization batch.

---

## Issue A: environment persistence anomaly after large single-call elaborations

### Symptom (worker's own words, from its status trace)

1. The worker sent its complete accumulated block (batches A–D, several hundred
   lines, ~30 declarations) as ONE `lean_repl` call. The call answered
   success ("The complete block compiles with no `sorryAx`").
2. In the NEXT call, the declarations were gone. Worker: "The big batch's
   declarations vanished between calls despite elaborating in-call. Let me
   diagnose what persisted" — its persistence spot-check came back empty.
3. Worker fell back to re-sending smaller sequential batches, verifying
   persistence after each — those persisted fine across calls.
4. Around the same time the service recorded `lastRestartReason: "Lean REPL
   exited (1)"` with `processGroupMembers: 0` — the REPL process died with
   exit code 1 (plausibly OOM: loaded environment ~7.6 GB RSS on a 9 GB
   machine, mid-way through the large elaboration; see issue D).

### Candidate root causes (builder to determine)

(a) The large call crashed the process *after* the success message was
    emitted, and the worker's stale `env`/`repl` handle kept pointing at the
    dead generation — the "vanishing" is the stale-handle path behaving
    correctly but being undetectable from the worker's side.
(b) The service's environment bookkeeping can desynchronize from the actual
    Lean process environment under large elaborations (an env counter that
    advances without the corresponding `lib.envs` entry surviving — cf. the
    "silent import swallowing" family of bugs from the previous report).
(c) Something in `request()` drops or replaces the stored environment when a
    large payload forces a buffer/streaming path.

### Impact

A worker can believe a large verified batch is safely in the environment and
build follow-up work on it, only to have it vanish. In this session the
worker detected it (persisted-verification habit) — a worker without that
habit would have produced proofs against phantom prerequisites. This is the
same trust-the-service failure family as the previous empty-environment bug.

### Requested

Root-cause diagnosis of what happens to a successfully-elaborated large call
when the process dies or the call is near a resource limit, and a guarantee:
either "a returned env handle is durable for the lifetime of the process
generation" or a loud error distinguishing the stale case. Note the stale
handle today returns a *generic* retry-from-new-root notice only sometimes;
workers have no way to detect that a specific env they just elaborated is gone.

---

## Issue B: restart-counter semantics conflate deliberate restarts with crashes

### Symptom

The counter reached 23 in one session. Breakdown: ~19 restarts were the
worker's *deliberate* strategy (it treated scratch pollution as persistent and
reset the shared service after every failed batch iteration — see Issue C and
the protocol note below); a handful were crash-recoveries including one exit
(1). A main agent reading `restartCount: 23` cannot tell "worker is misusing
the service" from "toolchain is crashing".

### Requested

Separate counters (or a reason-tagged log) for:
- request-triggered respawns after genuine process death (crash/OOM),
- respawns triggered while the previous process was still alive (deliberate
  misuse — see protocol note),
- main-agent-initiated re-imports.

---

## Issue C: worker-triggered respawn invalidates OTHER workers (shared singleton)

### Symptom / design gap

The recovery fix gave workers request-triggered auto-recovery. But the
service is a shared singleton: a respawn wipes the environment for every
session, so with 4 concurrent workers, one worker's recovery silently
invalidates the other workers' in-flight env handles (stale-handle errors
mid-proof). In this session the singleton worker *itself* triggered 23
respawns; in a 4-worker batch this would be mutual destruction.

### Requested

Gate worker-triggered recovery: if other sessions hold live references to the
same service, a worker's failed request must fail fast with the loud
`REPL-DOWN` error (letting main decide — e.g. abort or drain the other
workers first); automatic respawn only when the failing session is the sole
reference holder. Main-agent-triggered `lean_repl_import` remains
unguarded.

---

## Issue D: memory envelope

Loaded environment ~7.6 GB RSS on a 9 GB machine. Large elaborations (big
single-call blocks) plausibly caused the `exit (1)` observed under load. Not a
code fix per se, but worth: (i) confirming/refuting the OOM hypothesis from
the exit-code-1 event, (ii) documenting a practical per-call size guidance in
LEAN_REPL_GENERAL.md if confirmed.

---

## Related protocol note (main-agent-owned, filed for completeness)

The deliberate-restart pattern above rests on a misunderstanding the worker
protocol can eliminate: failed `sorryAx` declarations pollute only the
*branch* created by a call's `env` handle. Dropping the handle (omitting
`env`) starts a fresh branch from the clean shared root — no restart needed.
This is being added to SUBAGENTS.md / the lean worker prompt guidelines by the
main agent (not a builder task).

---

## Design decision (ratified by user, 2026-09-18): Option 2 — disposable-state-by-design

The policy question in this report (who may authorize destruction of the shared
environment) is resolved as follows:

- **No consent layer.** Sub sessions do not get to decide or veto recovery;
  there is no ack handshake. The service may respawn at any time — after a
  crash, after a timeout, or as part of recovery — without asking sessions.
- **The only durable state is the import block.** All session scratch state
  (env handles, in-flight declarations) is disposable by design. Subs are
  documented (LEAN_REPL_GENERAL.md, SUBAGENTS.md) to never depend on the
  shared environment surviving a respawn: work must be emitted (code text,
  file, commit) or be re-derivable from the root by re-elaboration.
- **Respawn must be loud:** on every respawn, the service state (generation
  counter, `downSince`/reset timestamp) must make the reset visible, and the
  next request's response must make the generation change detectable.
- **Precondition (issue A):** this policy is only workable if a returned env
  handle is durable within a process generation (no silent vanishing of
  successfully elaborated batches) — issue A's fix is required regardless.
- Builder work list under this decision: issue A fix; loud respawn signals;
  issue B (reason-tagged restart counters); issue C *dissolves* — no gating
  mechanism is to be built. Docs already updated on the sub side by main.

---

## Main-agent verification of builder resolution 0b3a7cf (2026-09-19)

All claims verified live in a fresh `pi -p` session (new extension code):
- Bare stale env (`env 99`, no `repl`) refused loudly with the documented
  message ("Bare environment 99 does not address the current root
  environment 0 ..."). ✓
- Bare root env (`env 0`, no `repl`) accepted, as documented. ✓
- Stale `repl` pair (`env 7`, `repl '99:1'`) rejected loudly. ✓
- Every response carries `generation`; `lean_repl_status` reports
  `restarts {crash, timeout, import}`, `recentRestarts`, and first
  initialization is not counted. ✓
- Docs (LEAN_REPL_GENERAL.md "Session state", LEAN_REPL_MAIN.md "Restart
  accounting") match observed behavior. ✓

**Correction (main-agent error in the original report):** the "19 deliberate
restarts" attributed to worker behavior in the original feedback were *main-
agent-initiated*: explicit `bash kill -TERM` of the process group (to force a
clean re-import after a rebuild) and `lean_repl_import` calls (import
respawns). The builder is right that workers cannot produce them. The
remaining restarts are consistent with timeout respawns of oversized calls.

## New issue (E): concurrent sessions spawn duplicate REPL generations (OOM risk)

Observed: a second pi session (`pi -p`) calling `lean_repl_import` spawned its
own live REPL generation (`1:14878`) instead of attaching to the already-
running healthy generation (`28:14772`) of the first session; the health field
of the second flagged the first as "unexpected project REPL process groups".
Two loaded generations ≈ 15 GB RSS on a 9.9 GB host — precisely the OOM regime
that (per the issue-A diagnosis) kills generations with exit(1).

Goal: make the intended singleton semantics unambiguous and OOM-safe. Either
(a) a session's `lean_repl_import` attaches to an existing healthy generation
with a compatible import block (true project-wide singleton), or (b) per-
session generations are intended — then the "unexpected project REPL process
groups" warning is misleading and should be replaced by documented isolation,
plus a loud guard refusing a second import while a loaded generation exists
(concurrent sessions on one host are then explicitly unsupported). Either way,
the current state (silent duplication + a warning that nobody can act on) is
the worst of both.

## Main-agent verification of builder resolution a270b63 (issue E, 2026-09-19)

Verified live with a foreign second pi process against main's loaded
generation `1:17945`:
- Import refused verbatim: `REPL-CONFLICT: another process already runs a REPL
  generation for this project: group 17945 (pids 17945,17996, ~7354 MB RSS).
  ... free it first with 'kill -9 -- -<pid>' and retry.` — no duplicate
  spawned (`projectReplProcesses: 0` from the foreign session's view). ✓
- Status warning is the new actionable text (group, RSS, both remedies). ✓
- Main's own generation untouched and healthy after the refused attempts;
  warning list empty from the owning session's view. ✓
- Worker promptGuidelines now cover `REPL-CONFLICT` alongside `REPL-DOWN`. ✓
- Docs (LEAN_REPL_GENERAL.md singleton note, LEAN_REPL_MAIN.md "One generation
  per project") match observed behavior. ✓
- Auditor premise correction accepted: `audit_launch` runs in-process with
  read/grep/bash/edit only — no auditor-specific step needed.

Issue E CLOSED. Parallel worker batches for chapter 2 are unblocked from the
REPL side.
