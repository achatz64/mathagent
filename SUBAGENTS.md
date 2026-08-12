# Managed subagents

Pi loads the project-local managed-subagent extension from
`.pi/extensions/subagents/`. Its profiles and concurrency limit are configured in
`.pi/subagents.json`.

## Proof-worker workflow

The main agent owns source interpretation, theorem and interface design,
integration, semantic review, builds, and commits. Lean proof workers are
read-only helpers: use the `lean` profile, which grants only `read`, `grep`, and
`lean_repl`. Do not give them Bash, editing, writing, worktrees, or builds.

A proof-worker prompt must be self-contained. Include:

1. the complete source statement, including every hypothesis and conclusion;
2. the complete source proof or argument, not only a citation or label;
3. relevant existing declarations and the intended insertion namespace;
4. semantic requirements for the final theorem type;
5. instructions to prefer reusable general APIs, avoid axioms, check every final
   declaration in `lean_repl`, and return paste-ready code;
6. likely namespaces, declaration fragments, and Mathlib source paths so the
   worker can search narrowly rather than rediscovering the whole API;
7. a request to report the REPL PID, approximate call count, timeouts, and
   perceived latency when testing infrastructure.

The supplied source proof is authoritative and is the worker's required
implementation plan, not optional background. The worker translates it
independently within interfaces chosen by the main agent. Failure to find an
exact library theorem is not a blocker: routine and representation-independent
helper lemmas remain proof work.

When translation reaches a genuine architectural representation choice not
fixed by the prompt, interface design returns to the main agent. The worker must
return a structured `INTERFACE REQUEST` containing:

1. the mathematical construction required by the source proof;
2. the Lean objects and APIs already found;
3. the exact type-level mismatch;
4. the smallest declarations or operations requiring a design decision;
5. all REPL-checked code completed before the boundary.

A vague API survey, list of missing lemmas, or recommendation for future work is
not an interface request. The main agent reviews the boundary, supplies exact
signatures and representation decisions with `subagent_send`, and the same
worker continues in its existing session. A true blocker remains limited to a
false statement, a missing essential hypothesis, or a circular source argument.
Loss of one REPL generation is not a blocker: retry from the replacement root
and re-elaborate the required local
declarations. Report an infrastructure blocker only after reproducible recovery
failure.

Workers can forget this distinction after several follow-ups and regress to
progress reports about routine elaboration. Review every intermediate response
immediately. If a worker labels ordinary coercion plumbing, missing project-local
imports, an absent packaged theorem, a failed tactic, or an unfinished helper as
a blocker, reply in the same session with an explicit `INVALID STOP` reminder:
identify why it is proof work, restate the relevant protocol rule, narrow the
next deliverable when useful, and require continued REPL checking. Do not accept
or collect an invalid stop merely because the worker accurately described its
residual goal. Conversely, do not reject a genuine representation choice: the
main agent must decide that interface and send exact signatures before asking
the worker to continue.

Reminders are not durable across later worker turns. Repeat them immediately
whenever the behavior recurs. A productive pattern is: accept the newly checked
fragment, reject only the attempted stop, provide the next concrete construction,
and keep the same session alive.

Do not ask a worker to decide whether an actionable audit gap may be deferred.
It may return a proof or a precise blocker under the standard above. The main
agent reviews whether the returned declaration actually exposes all source
clauses.

## Scheduling and tool sequence

Keep the main agent and all useful worker slots productive. When independent
proof, source-extraction, API-search, audit, or consolidation tasks are
available, launch them up to the configured concurrency limit. As workers run,
the main agent continues integration, semantic review, REPL checking,
documentation, or infrastructure work; it must not wait merely because one
worker is live.

Wait for a worker only when its result is the next actual dependency and no
independent main-agent work remains. Before waiting, fill any idle worker slots
with useful independent tasks where possible. Do not manufacture redundant work
just to occupy a slot, and do not queue several known heartbeat-heavy Lean
requests concurrently because the shared REPL serializes them.

There is currently no automatic worker deadline. Do not enter an unbounded wait
while useful work remains. Check `subagent_status` at natural checkpoints and
manually abort or reassign a worker whose elapsed time or lack of progress
exceeds the task's stated deadline. At the same checkpoints, inspect
`lean_repl_status`: worker state alone does not reveal a blocked shared queue,
repeated generations, process leaks, or memory pressure. Check OS process and
memory state immediately after any REPL timeout/restart or unexplained latency.
Do not start a target build while long worker REPL calls remain active.

- Launch independent tasks with `subagent_spawn`; parallel calls are preferred.
- Use profile name `lean` exactly. The tested limit is four concurrent workers.
- Use `subagent_send` to steer a live worker without restarting it. Include an
  immediate protocol reminder when the previous response was an invalid stop.
- Use `subagent_status` for nonblocking inspection. Its response also includes
  shared Lean REPL health, so review the worker and queue/process state together.
- For multiple live workers, use `subagent_wait_any` with their IDs. It returns
  as soon as one worker completes, allowing immediate review and follow-up;
  remove that worker from the next watched set and wait again.
- Use `subagent_wait` when watching one worker. Never wrap several waits in
  `multi_tool_use.parallel`: that creates an all-workers barrier and delays
  handling a worker that completed early. Never poll through Bash.
  After every `subagent_send`, register another wait before ending the turn;
  completion events are not delivered across turns without an active wait.
- After a first completion, inspect whether the result is final code or an
  `INTERFACE REQUEST`. For a request, use `subagent_send` and continue the same
  worker; do not collect it yet.
- Use `subagent_collect` with disposal only after successful final output or a
  decision to abandon the task. Abort only genuinely obsolete work.

Workers are read-only: returned code is not integrated merely because a worker
reports REPL success. The main agent must:

1. inspect the declaration types for source faithfulness and reusable design;
2. integrate the code into the proper namespace and architectural location;
3. reproduce or extend checks in the main shared REPL when needed;
4. run the target `lake build`;
5. update the audit ledger only after the successful build;
6. run coverage and `git diff --check`, then commit.

Never report worker output as integrated before completing these steps.

## Verification and consolidation discipline

A worker's statement that code was “REPL-checked” is an untrusted report, not a
validation artifact. Scratch environments can contain undeclared aliases,
earlier experimental axioms, stale versions of project declarations, or
prerequisites omitted from the returned text. A successful `#print axioms` also
checks only the elaborated declaration's logical dependencies; it does not show
that the returned chunk is self-contained or semantically faithful.

For every substantial returned proof:

1. reject fabricated witnesses, placeholder choices, aliases to scratch names,
   and any declaration whose construction is not visible in the returned code;
2. require declarations in dependency order, with no forward references and no
   reliance on the compiled target theorem being replaced;
3. replay the complete returned chunk from the shared Mathlib root, explicitly
   re-elaborating the minimal project-local prerequisites;
4. inspect `#print axioms` for each final public result and important helper;
5. only then integrate it and run the target build.

A worker should normally return one self-contained block replayed from the clean
Mathlib root. If response size requires sequential blocks, each block may depend
only on Mathlib and previously accepted blocks, must use final names in the
intended ambient namespace, and must contain no unreturned scratch dependency.
Partial scratch chunks are mathematical evidence, not integration material. If
clean consolidation repeatedly fails, preserve the last known-good target and
hand the mathematical construction—not the claimed final status—to another
worker. The same rule applies to performance: if an integrated worker block
causes deterministic kernel timeouts or a major build time/RSS regression,
restore the known-good target immediately. Do not increase `maxHeartbeats` to
turn an unverified worker proof into a long-running full-file experiment.

Lean declaration kinds matter during review: use `theorem` only for
propositions. Constructions returning data such as equivalences, bases, or
representations must be `def`/`noncomputable def` (or an appropriately typed
`let`), even if a worker presents them as theorem-like helpers.

## Shared Lean REPL

Main and worker SDK sessions share one project REPL process. Model reasoning is
parallel, while Lean requests are serialized through a FIFO queue. Four workers
have been tested successfully on substantial proofs with ordinary perceived
latency generally below a few seconds.

An `env` is meaningful only in the REPL generation that created it. When an
environment is retained across turns or explicitly handed to a worker, pass both
its `env` and `repl` values. Workers may otherwise omit `env` to branch from the
shared Mathlib root. One slow elaboration blocks the queue, so split exploratory
checks into bounded commands and avoid submitting known heartbeat-heavy commands
from several workers at once. Before spawning multiple Lean workers, record a
healthy `lean_repl_status` baseline. During a four-worker experiment, check the
status at the first process checkpoint and at each natural integration point.
If `pendingRequests` grows, active request age approaches 120 seconds, restart
count increases, or the process group has other than the expected launcher and
REPL pair, stop adding work and diagnose before continuing. Before a full target
build, abort obsolete workers, drain the queue, and account for resident REPL
memory. Measure diagnostic builds with elapsed time and peak RSS and compare to
the last known-good target; a large regression after a small integration is a
proof problem until shown otherwise, not merely a slow import phase.

## Safe Mathlib discovery

Never use Lean's `#find` in the shared REPL. Broad `#find` searches can exceed
the transport timeout and terminate the process for every worker. Proof-worker
prompts should explicitly prohibit it and direct workers to this sequence:

1. use `grep` narrowly in `lean/.lake/packages/mathlib/Mathlib` for guessed
   declaration fragments, carrier types, or interface words such as `ker`,
   `quotient`, `centralizer`, and `finrank`;
2. use `read` on the matching file to inspect neighboring declarations and the
   intended namespace;
3. verify exact candidates with targeted `#check`, `#print`, or `#synth`;
4. test candidates in small examples before checking a full proof block.

The shared REPL root has already executed `import Mathlib`. Never send an
`import` command through `lean_repl`: imports are only legal at the beginning of
a Lean input file, whereas tool calls elaborate within an existing environment.
The persistent target (for example `GT.lean`) is not imported into that root.
A worker using project-local prerequisites must read them from the target and
paste the smallest relevant declarations into its branch, renaming a declaration
when necessary to avoid testing the theorem against its previously compiled
version. A worker may only claim REPL verification for dependencies available
from Mathlib or explicitly elaborated in its returned environment.

The main agent should supply likely APIs and source paths whenever known. Search
output must remain narrow; do not replace `#find` with an unbounded repository
regular expression.
