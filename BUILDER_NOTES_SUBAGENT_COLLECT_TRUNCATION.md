# Builder notes — subagent deliverable truncation via `subagent_collect` (new, unreported issue)

**Date:** 2026-10-11 (chapter-IV main session)
**Component:** `.pi/extensions/subagents/` (index.ts — collect/wait tooling)

## Issue: `subagent_collect` returns only the LAST assistant message

**Mechanism (observed twice, same session, 30 minutes apart):**

A worker that finalizes over several assistant messages (e.g. an intermediate
"assembling the final version now..." message followed by the actual deliverable,
or a long stream punctuated by REPL restarts) delivers everything in memory, but
`subagent_collect` returns **only its final assistant message**. Everything before
it in the finalization sequence is unreachable — and if the worker was disposed
at collect time (the normal flow), it is permanently gone.

**Confirmed incidents (chapter IV, workers w28 and w29, 2026-10-11):**

1. **w28 (S₄/Klein reconstruction).** Its status stream showed a complete
   verification campaign (Part A built, multiplication table, card, normality,
   then Parts B–D assembled, a genuine staging bug found in
   `quarticPairingIdx_perm` — mis-ordered `quarticPairingIdx_compl` arguments —
   plus an `open FT` fix). Its collect returned only the last message: a
   mid-sentence fragment ("Section 2 revealed two things: ... Let me check what
   got phantom-committed:"). The entire Part A source and the fix diff were
   lost; the task had to be re-derived.
2. **w29 (cg22 finish).** Stream showed it fixing the `orderOf_swap_mul_cycle3_eq_six`
   tail and drafting the three missing sections. Collect returned only
   "Fixing the decomposition endings and the not-dvd block:" — truncated. Its
   completed sections (a) `isSwap_of_mem_of_cycleType23`, (b)
   `top_of_swap_and_primeCycle`, (c) the cg22 assembly were lost.

**Relationship to the known failure modes (SUBAGENTS.md, "persist on receipt"):**

- *Compaction loss* (codified 2026-10-10): worker content lives only in main's
  conversation until main stages it; compaction destroys it. Mitigation exists.
- *Collect truncation* (this note): a NEW mechanism — even the diligent flow
  "collect then stage" fails, because the collect itself no longer contains the
  full deliverable. Main cannot stage what collect does not return.

## Remedies requested

1. **`subagent_collect` should return the worker's full transcript tail**
   (e.g. all messages since the last `subagent_send`/spawn), or at least
   concatenate all assistant messages of the final turn sequence — not only the
   last one. Size-capping with an explicit `truncated: true` marker would be
   acceptable.
2. **Alternative (smaller):** a `subagent_status`-style raw-transcript read tool
   (read-only), so main can pull earlier messages of a live-or-done worker after
   noticing a truncated collect. Even better for done workers: keep the last
   N messages readable for disposed workers (a bounded dead-letter buffer).
3. **Tool-contract fix (cheap, do regardless):** document on `subagent_collect`
   that only the final assistant message is returned, so mains know to require
   single-message finalization from workers.

## Interim main-agent discipline (in force until fixed)

- Worker prompts should REQUIRE: "your FINAL REPLY must be ONE message containing
  the complete deliverable verbatim; never split the final deliverable across
  messages." (Chapter-IV prompts now carry this; w28/w29 predate it.)
- If a collect comes back mid-sentence or missing promised sections, treat the
  content as lost immediately — do not wait/retry the worker; re-derive. Status
  polling (`latestText`) is the only way to salvage fragments of a still-live
  worker, and it shows only the newest message fragment.
- All substantive verified content must ALSO be streamed via progress updates
  (which main reads and can stage incrementally) — but note `latestText` in
  status is likewise a fragment, not a stream archive.

## Related records

- `BUILDER_NOTES_REPL_SESSION_STATE.md` (REPL-side loss mechanisms, delivered).
- `BUILDER_FEEDBACK_SAME_GEN_DECL_LOSS.md` (declaration loss within a live
  generation, delivered).
- `SUBAGENTS.md` "Persist on receipt" (compaction loss, process mitigation).
