# Managed subagents

Pi loads the project-local managed-subagent extension from
`.pi/extensions/subagents/`. Its profiles and concurrency limit are configured in
`.pi/subagents.json`.

## Proof-worker workflow

The main agent owns source interpretation, theorem statement design, integration,
semantic review, builds, and commits. Lean proof workers are read-only helpers:
use the `lean` profile, which grants only `read`, `grep`, and `lean_repl`. Do not
give them Bash, editing, writing, worktrees, or builds.

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
implementation plan, not optional background. The worker must translate it
independently down to lower-level Mathlib APIs and prove every intermediate
bridge it requires. Failure to find an exact library theorem, the size of a
missing lemma, or the absence of a project-local bridge is not a blocker and
must not end the task. Search is only for proof plumbing; after search, the
worker constructs and tests the argument given in the prompt.

A Lean worker must not return an API survey, a list of missing lemmas, or a
recommendation for future work. A valid blocker is limited to a false statement,
a genuinely missing essential hypothesis or circular source argument, or loss
of the REPL process itself. Ordinary elaboration errors and substantial helper
lemmas are proof work, not blockers.

Do not ask a worker to decide whether an actionable audit gap may be deferred.
It may return a proof or a precise blocker under the standard above. The main
agent reviews whether the returned declaration actually exposes all source
clauses.

## Tool sequence

- Launch independent tasks with `subagent_spawn`; parallel calls are preferred.
- Use profile name `lean` exactly. The tested limit is four concurrent workers.
- Use `subagent_send` to steer a live worker without restarting it.
- Use `subagent_status` for nonblocking inspection.
- Use `subagent_wait` for event-driven completion; never poll through Bash.
- Use `subagent_collect` with disposal after completion to retrieve output and
  release the worker session. Abort only genuinely obsolete work.

Workers are read-only: returned code is not integrated merely because a worker
reports REPL success. The main agent must:

1. inspect the declaration types for source faithfulness and reusable design;
2. integrate the code into the proper namespace and architectural location;
3. reproduce or extend checks in the main shared REPL when needed;
4. run the target `lake build`;
5. update the audit ledger only after the successful build;
6. run coverage and `git diff --check`, then commit.

Never report worker output as integrated before completing these steps.

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
from several workers at once.

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
