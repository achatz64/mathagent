# Builder issue report — managed subagents: worker identification and REPL import race

Reported by: main formalization agent (FT/Milne-FT v5.00 session, 2026-09-17)
Component: `.pi/extensions/subagents/` (managed-subagent extension) and its
interaction with the shared Lean REPL. Extension source lives in
`.pi/extensions/subagents/`; REPL behavior in `.pi/extensions/lean-repl/`.

These are bug reports, not designs. Suggested fixes are optional input; the
builder owns the implementation.

---

## Issue 1 (previously flagged as #3): worker id ↔ task mapping is opaque

### Symptom

With several workers spawned in one turn, the main agent cannot tell which
returned result belongs to which task without reading the result body:

- The `w1..w4` ids assigned by the extension do not correspond to spawn call
  order (two sessions in a row the labels appeared reversed/scrambled relative
  to the spawn order).
- During the FT session, `subagent_wait_any` returned a result whose content
  belonged to a different task than the id it was filed under; a follow-up
  wait re-delivered an already-collected completion (see Issue 2), and both
  times the id/content mismatch had to be resolved by inspecting the result
  text.

### Impact

The main agent must content-match every result before integration. With
parallel proof workers returning similar-looking Lean blocks this is error
prone (a wrong-task integration would be caught only at build/audit time) and
wastes review cycles.

### Suggested fix (optional)

Echo a client-supplied task tag (or the first line of the task prompt) in:

- every `subagent_status` entry (next to `id`/`state`/`latestText`),
- the `subagent_wait_any` / `subagent_wait` completion events,
- the `subagent_collect` output.

## Issue 2 (previously flagged as #4): `wait_any` re-delivers already-collected completions

### Symptom

Observed twice in the FT session. Sequence:

1. `subagent_wait_any(ids)` returns worker X's completion; the main agent
   reviews, integrates, and commits it.
2. A later `subagent_wait_any(ids)` (same or overlapping id set) returns
   worker X's *same* completion text again, instead of waiting for a still
   running worker in the set.

### Impact

One wasted review cycle per occurrence; worse, it breaks the main agent's
protocol assumption that "a completion event means new, unreviewed output",
which can lead to double-integration attempts.

### Suggested fix (optional)

`wait_any` should skip workers whose completion has already been delivered to
(and collected by) the main agent in this session; if all watched workers are
already collected, it should either block on the live ones or return an
explicit "no uncollected completions in watched set" response instead of
replaying buffered output.

## Issue 3 (previously flagged as #5): `lean_repl_import` race with automatic restart

### Symptom

Sequence observed in the FT session, reproducible whenever a target rebuild is
followed by a REPL restart while workers are live:

1. Main agent rebuilds the target (`lake build Target`).
2. Main agent kills the REPL process group (`kill -TERM -- -<pid>`).
3. Main agent calls `lean_repl_import` with the (unchanged) import block.
4. The call is **refused**: "REPL already initialized — use bash to kill the
   process first".

Root cause: between step 2 and step 3, a queued worker request hit the dead
REPL and triggered the *automatic restart on request*. The auto-restart used
the last configured import block, so by the time step 3 arrived, a live REPL
already existed and `lean_repl_import`'s "refuse on live REPL" guard fired.

### Impact

- Benign in the observed case (auto-restart reused the same import block), but
  the refusal reads as an error and the main agent cannot distinguish
  "already running with the imports I want" from "running with wrong imports".
- Latent risk: if the auto-restart ever picks up a stale import block (e.g.
  after an intended import change is lost in the race), the REPL root silently
  diverges from what the main agent believes it configured.

### Suggested fix (optional)

Make `lean_repl_import` idempotent: if the live REPL's active import block is
exactly the requested one, succeed as a no-op and report that state (e.g.
`{"status": "already-running", "imports": ...}`) instead of refusing; keep the
refusal for genuine import-block changes on a live REPL. Additionally,
document in `LEAN_REPL_GENERAL.md` that an automatic restart on request
reuses the last configured import block.

---

## Issue 4 (new): auditor launcher for the main agent

### Background

Audits are currently launched by the main agent as a headless `pi -p` call
with a hand-written prompt file (see `tmp/audit_ft_ch1_prompt.md` for the FT
example). This has a structural conflict of interest: the party being audited
authors the briefing, and in the FT session the first draft indeed overstepped
by prescribing the audit scope, pre-ranking risk items, and excluding material
— it had to be killed and relaunched with a neutral prompt.

### Requested capability

A launcher (extension tool or script) that starts an auditor agent for the
main agent, with the following hard requirements:

1. **No prompt injection.** The launcher takes NO arguments from the main
   agent — no prompt text, no scope, no file lists, no "focus areas". All
   auditor-facing content must come from fixed, committed repository material
   (AGENTS.md, RULES.md, AUDIT.md, the target itself, its provenance header,
   and the INVENTORY/COVERAGE script hooks). The auditor determines its own
   scope from AUDIT.md.
2. **Synchronous.** Not a background launch: the call blocks, and when it
   returns, the audit is finished. The main agent then picks up the audit
   result directly from the target (e.g. `AUDIT-GAP` markers) and the audit
   deliverable commit.

### Impact if not built

Every future audit either repeats the main-agent-prompt conflict of interest,
or requires ad-hoc manual discipline (as in this session) that does not
survive agent turnover.

### Suggested fix (optional)

The launcher itself embeds the auditor briefing (role, pre-reading list,
protocol) and injects exactly two fixed facts: the audit target — by default
`lean/Target.lean` — and the deliverable rule (one commit; main picks up
`AUDIT-GAP` markers and the deliverable commit when the call returns). No
briefing file is added to the repository.

Making the target configurable (so the launcher can later serve other targets, e.g. audited promotion candidates)
is deferred future work; the first version is allowed to hard-code
`lean/Target.lean`. 



---

## Builder resolution (2026-09-17)

All four issues investigated and confirmed real. Fixes implemented and tested
with fresh `pi -p` processes (TESTING.md).

- **Issue 1 — fixed.** `subagent_spawn` takes an optional `label` (defaults to
  the first task line, whitespace-collapsed, truncated to 80 chars). The label
  is echoed in `subagent_status` snapshots, in spawn/wait/wait_any/collect
  content text (`wN (label)` first line), and in failed-worker errors. Note:
  the id-scrambling symptom is explained by id assignment at spawn *completion*
  order, not call order; ids remain completion-ordered — match by label.
  Documented in SUBAGENTS.md.
- **Issue 2 — fixed.** Workers carry a `delivered` flag, set when
  wait/wait_any/collect hands the current result to the caller and reset by
  `subagent_send`. `wait_any` prefers undelivered completions, otherwise waits
  on live workers, and returns an explicit "No uncollected completions in the
  watched set" response instead of replaying. Tested: no replay, explicit
  no-uncollected message. SUBAGENTS.md watch-set guidance updated.
- **Issue 3 — fixed.** `lean_repl_import` is now idempotent: if the live REPL's
  import block matches the request (after trim), it succeeds as a no-op and
  reports `status: "already-running"`; a different import block on a live REPL
  still refuses with an explicit "different import block" message. Response
  carries a `status` field (`initialized` | `already-running`). Documented in
  LEAN_REPL_MAIN.md and LEAN_REPL_GENERAL.md (auto-restart reuse of the last
  import block was already documented there).
- **Issue 4 — built.** New extension `.pi/extensions/auditor/index.ts` with
  tool `audit_launch`: zero parameters, synchronous (blocks until the audit is
  finished), embedded briefing (role, mandatory pre-reading AGENTS.md →
  RULES.md → AUDIT.md → PROVENANCE.md → target incl. provenance header and
  INVENTORY/COVERAGE hooks → FORMALIZATION.md, self-determined scope,
  AUDIT-GAP-only edit rights, no .pi/ or documentation changes). Injects
  exactly two fixed facts: target `lean/Target.lean` and the deliverable rule
  (markers in target + exactly one commit, message beginning `audit: `).
  Tools: read, grep, bash, edit. Concurrency guard: one audit at a time.
  Smoke-tested end to end (session machinery, briefing delivery, clean
  exit); no briefing file added to the repository.
