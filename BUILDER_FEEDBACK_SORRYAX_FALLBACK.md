# Builder issue: shared REPL silently commits declarations with `sorryAx` after a failed tactic

**Status:** open (2026-10-11, main)
**Component:** the shared REPL service (`.pi/extensions/lean-repl/` wrapping
`lean/.lake/packages/repl/`) — exact layer (repl binary vs extension) to be
localized by the builder.

## Observed mechanism

When a declaration's elaboration fails (tactic error, whnf timeout, unsolved
goals), the REPL sometimes **commits the declaration anyway with a
`sorryAx`-fallback proof** and continues the session silently. The command
response reports the elaboration error, but the environment now contains a
tainted declaration under the intended name. Everything downstream elaborates
"successfully" against it — the taint is invisible except through
`#print axioms`, which then shows `sorryAx` in the dependency list.

## Evidence (three independent hits in one day)

1. **Main session (2026-10-11):** the first elaboration attempt of the w31
   block's `quarticPairingIdx_perm` failed in two branches (crossed `rw`
   names). A subsequent `#print axioms FT.quarticPairingIdx_perm` printed
   `[propext, sorryAx, Classical.choice, Quot.sound]` — the declaration had
   been committed with the fallback despite the reported errors.
2. **Worker w32 (cg22):** reported "the REPL silently inserted sorry-fallbacks
   after a whnf timeout/failed tactic in three intermediate runs"; caught all
   of them by the mandated axiom batch and re-proved (`not_dvd_quad_c1_2_c0_1`,
   `not_dvd_quad_X5_add_2X_add_2`, `irreducible_X5_add_2X_add_2_ZMod3`).
3. **Worker w31 (S₄/Klein):** same pattern — first failed batches committed
   tainted declarations under the final names, forcing tmp-name re-verification
   (`quarticKlein_card_tmp` etc.) and a fresh one-shot re-run.

## Why it matters

- A worker that does not run the axiom batch (or runs it mid-session and then
  re-elaborates) can deliver tainted "verified" code. The axiom batch is
  currently the ONLY detection mechanism; it has now been promoted to a
  mandatory, last-step item in every worker brief (SUBAGENTS.md).
- Tainted names persist for the whole generation: re-sending the declaration
  under the same name fails with "already been declared", forcing renames and
  wasted verification passes (w31's tmp-name detour).

## Suggested fixes (builder to triage)

1. Make the sorry-fallback opt-in, or drop it entirely: a failed elaboration
   should NOT add the declaration to the environment (current Mathlib repl
   tooling has options for this; surface one).
2. If the fallback stays: report it loudly in the command response
   (e.g. `warning: declaration X committed with sorryAx fallback`), and have
   `lean_repl_status` expose a per-generation taint counter so workers and main
   can detect it without re-printing axioms.
3. Cheap worker-side mitigation already in place: the axiom batch mandate.
