# Lean linter fixes

Workflow for clearing linter warnings from a target `*.lean` file.

1. Collect warnings from `lake build {target}`. Each warning gives an
   exact `line:col` and the suggested fix. Read only those regions.

2. Pre-check risky rewrites in `lean_repl` before editing the file. In
   particular, any change to tactic combinators (`<;>` → `;`) or to
   `variable`/`omit` scope must be verified on a minimal example; build cycles
   are too expensive for trial-and-error.

3. Linter suggestions can be false positives. `unnecessarySeqFocus` may propose
   `(tac1; tac2)` when `tac1` silently closes one branch; the replacement then
   fails with "No goals to be solved". Restructure into explicit `·` bullets
   instead. Trust the *warning location*, verify the *suggested fix*.

4. Check `oldText` uniqueness with `grep -nF` before calling the editor: short
   snippets match as substrings of differently-indented lines and make the edit
   fail.

5. `unusedSectionVars` fixes cascade: omitting an unused instance exposes
   instances that depended on it. Re-check and omit all of them together,
   e.g. `omit [Invertible …] [Fintype G] in`.

6. Apply all edits in one batch, then run a single verification build; confirm
   zero `warning:` lines.
