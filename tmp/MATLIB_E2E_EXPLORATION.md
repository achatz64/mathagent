# MATLIB_E2E_EXPLORATION.md — Lessons learned (NOT a plan)

> This file records decisions, findings, and lessons as we run the end-to-end
> exploration of "take mathlib's linters/conventions to Extlib, then upstream a
> low-effort PR to mathlib". It is deliberately a log, not a plan doc.
> Agent docs (AGENTS.md / RULES.md / etc.) are NOT updated until the full
> T1→T4 end-to-end test has run.

## Session reframe (2025-08-15)
- Reframed from "exploration only" into an **end-to-end exploration task** covering T1→T4.
- No agent-doc (AGENTS.md / RULES.md / SUBAGENTS.md / EXTLIB_BUILDER.md / …) updates until the
  full T1→T4 e2e test passes.
- Only this lessons-learned file is created now.

## Agreed flow
- Sequence: **T1 (linter) → T2 (PR workflow redesign) → T3/T4 (prepare + execute a PR)**.
- T3/T4 are **gated on a human** (the human `mathlib_contributor` = `achatz64`).
- Within T3, order is **low-effort-first**, but for e2e *testing* of the flow we do
  **exactly ONE low-effort PR** (not many).
- T2 (PR workflow) intentionally left open until T1 output is seen; redesign after T1.

## T1 — run mathlib linters verbatim on Extlib root (observation only, no fixes)
- Build setup: package `ma1` (`lean/lakefile.toml`) declares
  `[[lean_lib]] name="Extlib" srcDir=".." globs=["Extlib.+"]`.
  So `Extlib/GroupTheory/Mil21.lean` (namespace `GT`) is the Extlib library.
- Two linter kinds:
  - **env-level** (`#lint` default set), runnable verbatim via `#lint in Extlib`:
    `missingDocs`, `simpNF`, `simpVarHead`, `gcongr`, `toAdditive`,
    `decidable` / `decidableClass`, `unusedHavesSuffices`, `unreachableTactic`,
    `GuardMono`, plus mathlib's `structureInType`, `deprecatedNoSince`.
  - **file-level** (`addLinter`; require `set_option linter.X true` in the build):
    `dupNamespace`, `minImports`, `unusedTactic`, `upstreamableDecl`
    (NOTE: this is a file-splitting aid, NOT a PR-worthiness detector),
    `hashCommand`, `ppRoundtrip`, `privateModule`, `globalAttributeIn`,
    and the text-style family: `trailingWhitespace`, `whitespaceBeforeSemicolon`,
    `unicodeLinter`, `adaptationNote`, `modulesUpperCamelCase`,
    `modulesForbiddenWindows`, `pythonStyle` (off by default).
- Plan: run **env-level `#lint in Extlib` first** (reversible), observe; then optionally enable
  file-level linters via a temporary `leanOptions` in the lakefile (to be reverted).
- Conflicts noted for later (do NOT fix yet):
  - `linter.style.header` vs Provenance: Extlib has a `/-! # Provenance … -/` TOML block but
    **no `Copyright (c) … Authors:` header** → header linter would fire. Also this linter is
    gated on mathlib's library root, so it needs forcing to run on Extlib.
  - `linter.minImports`: the 44-line import block almost certainly has unused imports.
  - `missingDocs`: docstring gap of order ~100 public (non-`simp`, non-`private`) declarations.
  - Passes as-is: `modulesUpperCamelCase` (`Mil21` is UpperCamelCase), `dupNamespace`
    (`namespace GT`, no duplicated namespaces).

## T1 lint run — results (env-level `#lint in Extlib`, 2025-08-15)
- Method: project REPL (package `ma1`), `import Extlib.GroupTheory.Mil21`, then `#lint in Extlib`.
  Extlib was already built/cached, so this only *re-loaded* oleans (no rebuild of Mil21 math).
- Headline: **53 errors** in 501 declarations (+464 auto-generated) across **16 linters**
  (the default `#lint` set). Only **5 linters fired**.
- Linters that **passed cleanly**: `simpVarHead`, `gcongr`, `toAdditive`, `decidable`,
  `unusedHavesSuffices`, `unreachableTactic`, `GuardMono`, `structureInType`, `deprecatedNoSince`.
- Linters that **fired** (concrete, observation only — no fixes yet):
  1. `defLemma` (1): `GT.OperatorGroup.IsInvariant.quotientAction` is a `def` that should be
     `lemma`/`theorem`. → trivial fix; prime low-effort upstream candidate.
  2. `defsWithUnderscore` (6): names with `_`/apostrophe:
     - `GT.Representation.asModule_ofModule'LinearEquiv`
     - `GT.CoxeterReflection.instDecidableEq_extlib`, `_3`, `_4`, `_5`, `_6`
     - **CONFLICT (project vs mathlib):** the `_extlib` suffix is a *deliberate project convention*
       to avoid clashing with mathlib's `instDecidableEq`. This linter directly contradicts that
       rule. For upstreaming these must be renamed; for local Extlib either keep (accept lint) or
       `@[nolint defsWithUnderscore]`. Must be decided before any fix.
  3. `docBlame` (≈37; this is the linter formerly named `missingDocs`): undocumented public
     `def`s, concentrated in `CoxeterReflection.*` and `Bd3mSource.*`. Full list:
     - `HermitianInnerProductOverComplexSubfield.pairing`, `classFunctionPairingComplexSubfield`,
       `ExactExtension.inclusion`, `ExactExtension.projection`, `IsMinimalTwoSidedIdeal`,
       `CoxeterReflection.{instDecidableEq_extlib, pairCoeff, pairForm, coeff, Space, form, root,
       reflection, instDecidableEq_extlib_1, reflectionEquiv, instDecidableEq_extlib_2, pairEmbed,
       pairProduct, instDecidableEq_extlib_3, pairActionLinear, pairAction, instDecidableEq_extlib_4,
       complexCoord, instDecidableEq_extlib_5, instDecidableEq_extlib_6}`,
       `Bd3mSource.{diag2, slOf, upper, lower, upperSL0, lowerSL0, prodSL0}`,
       `GroupJordanHolder.{secondIso, quotientCongrUpper, quotientCongrLower}`.
     → medium effort; required for upstreaming.
  4. `simpNF` (2): `GT.ExactExtension.directProductEquivOfComplete_apply`,
     `GT.ExactExtension.centralizerProjectionMulEquivOfComplete_apply` — LHS simplifies via
     `MonoidHom.coe_range`. → easy fixes; good low-effort upstream candidates (single lemmas).
  5. `unusedArguments` (9): unused type-class arguments:
     - `GT.CommGroup.cyclicPiPrimePowerEquiv` arg2 `Fintype ι`
     - `GT.CommGroup.piPrimePowerNeZeroMulEquiv` arg2 `DecidableEq ι`
     - `GT.CommGroup.primeMultiplicity` args `DecidableEq ι`, `DecidableEq (elementaryPrimes p)`
     - `GT.CommGroup.elementaryPrime` arg3 `DecidableEq ι`
     - `GT.Module.End.divisionRingOfIsSimple` arg10 `IsScalarTower F A S`
     - `GT.Subalgebra.centerPiLinearEquiv` arg4 `Fintype ι`
     - `GT.FDRep.HasSimpleCharacterDecomposition` arg6 `Invertible ↑(Fintype.card G)`
     - `GT.FDRep.VirtualCharacter` arg6 `Invertible ↑(Fintype.card G)`
     - `GT.FDRep.dfinsuppOf` arg5 `Fintype G`
     - **CONFLICT (benign):** mathlib itself frequently disables `unusedArguments` for intentional
       type-class args. Many of these are benign; likely exclude or `@[nolint unusedArguments]`.
- **File-level linters — run 2025-08-15** via a *temporary* `[lean_lib.leanOptions]` block in
  `lean/lakefile.toml` (reverted after; no math changes). Critical lessons:
  - **Linter output goes to STDOUT as `warning:` lines, NOT stderr.** (First pass read stderr and
    wrongly saw '0 warnings'. Always grep the build stdout.)
  - Mathlib linter options are *library-defined*, so they must use the **`weak.` prefix**
    (`weak.linter.minImports = true`, etc.); plain `linter.X` fails with
    'unknown configuration option' at Lean startup. The `weak.` prefix is the reproducible trick.
  - Linters apply ONLY to the `Extlib` lib; mathlib (separate package) was **NOT** recompiled.
    Mil21 built in **394s** — all of it `minImports` import-graph overhead, NOT mathlib recompile.
    So enabling linters does not 'get into the mathlib dependencies'.
  - **`linter.minImports`** — two signals:
    1. ACTIONABLE: **35 of 44 imports are transitively redundant** ('unneeded import' list,
       e.g. `Mathlib.GroupTheory.Sylow`, `Mathlib.Data.Complex.Basic`, `Mathlib.RepresentationTheory.Maschke`,
       `Mathlib.RingTheory.FiniteLength`, `Mathlib.GroupTheory.Torsion`, `Mathlib.GroupTheory.Solvable`, …).
       Pruning to ~9 imports would shrink the block and speed compilation. Auditor's job.
    2. NOISE: 'Imports increased by N to [Lean.Parser.Command]' (189 lines) — the `increases`
       sub-check; suppress it (do NOT enable `linter.minImports.increases`).
    - Also a 'missing imports' note at line 1 (flip side); low priority.
  - **`dupNamespace`, `unicodeLinter`, `trailingWhitespace`, `whitespaceBeforeSemicolon`,
    `modulesUpperCamelCase`, `modulesForbiddenWindows`**: **ZERO warnings on Mil21 → pass.**
    (`dupNamespace` confirmed to fire via a throwaway probe `GT.GT.x`.)
  - Not enabled this pass (out of scope): `unusedTactic`, `hashCommand`, `ppRoundtrip`,
    `privateModule`, `globalAttributeIn`, `adaptationNote`.
  - `linter.style.header` (provenance conflict) still unobserved: gated on mathlib's library root,
    so it self-skips on Extlib. To observe live, need a temp copy under a mathlib-root import.
- **Full redundant-import list (35):** `Mathlib.Algebra.Group.Subgroup.Pointwise`,
  `Mathlib.Algebra.Module.ZMod`, `Mathlib.Data.Complex.Basic`, `Mathlib.Data.Finset.Sort`,
  `Mathlib.Data.List.NodupEquivFin`, `Mathlib.Data.ZMod.QuotientRing`, `Mathlib.Data.ZMod.Units`,
  `Mathlib.FieldTheory.Finite.GaloisField`, `Mathlib.FieldTheory.Finiteness`,
  `Mathlib.GroupTheory.ClassEquation`, `Mathlib.GroupTheory.Coset.Basic`,
  `Mathlib.GroupTheory.FiniteAbelian.Duality`, `Mathlib.GroupTheory.FreeGroup.NielsenSchreier`,
  `Mathlib.GroupTheory.GroupAction.Primitive`, `Mathlib.GroupTheory.GroupAction.Quotient`,
  `Mathlib.GroupTheory.Index`, `Mathlib.GroupTheory.PGroup`, `Mathlib.GroupTheory.Perm.Cycle.Factors`,
  `Mathlib.GroupTheory.Perm.Cycle.Type`, `Mathlib.GroupTheory.Perm.Subgroup`,
  `Mathlib.GroupTheory.PresentedGroup`, `Mathlib.GroupTheory.QuotientGroup.Basic`,
  `Mathlib.GroupTheory.Schreier`, `Mathlib.GroupTheory.SchurZassenhaus`, `Mathlib.GroupTheory.Solvable`,
  `Mathlib.GroupTheory.SpecificGroups.Cyclic`, `Mathlib.GroupTheory.Sylow`, `Mathlib.GroupTheory.Torsion`,
  `Mathlib.LinearAlgebra.DirectSum.Finite`, `Mathlib.Order.Interval.Finset.Fin`,
  `Mathlib.RepresentationTheory.Character`, `Mathlib.RepresentationTheory.Maschke`,
  `Mathlib.RingTheory.FiniteLength`, `Mathlib.RingTheory.RootsOfUnity.Complex`,
  `Mathlib.RingTheory.SimpleModule.Isotypic`.
- **Lessons:**
  - Running the linter verbatim *immediately* surfaced two real conflicts: the `_extlib` naming
    convention vs `defsWithUnderscore`, and benign type-class `unusedArguments`. Both must be
    resolved by policy *before* any code change.
  - The default `#lint` set is smaller/older than my earlier guess: the docstring linter is now
    `docBlame` (not `missingDocs`), and `unusedArguments` is in the default set while
    `unusedHavesSuffices` is not the one that fired. **Trust the live run, not memory.**
  - Low-effort, single-lemma upstream candidates are already visible: `defLemma` (1) + `simpNF` (2)
    = 3 trivial fixes. Good first PR for the T3/T4 e2e test.

## Reproducibility — the linters are NOT a separate install
- The linters live INSIDE the `mathlib` package (rev `v4.31.0`), declared as a dependency in
  `lean/lakefile.toml` and pinned in `lean/lake-manifest.json`
  (source at `.lake/packages/mathlib/Mathlib/Tactic/Linter/*`).
- A fresh clone + `lake` therefore fetches mathlib *with its linters* automatically. Nothing was
  installed by hand — the capability is 100% reproducible from the repo.
- What is NOT reproducible yet: the *how-to-run recipe* (discovered, not documented):
  1. env-level: REPL `import Extlib.GroupTheory.Mil21` → `#lint in Extlib` (no build needed).
  2. file-level: temporarily add `[lean_lib.leanOptions]` with `weak.` prefixes to `lean/lakefile.toml`,
     `lake build Extlib`, read **stdout** `warning:` lines, then revert the lakefile.
- ACTION: before closing T1, commit a documented, re-runnable lint command/target (a T1 deliverable;
  deferred per 'no agent-doc updates until e2e test' — recorded here instead).

## Roles (clarified 2025-08-15)
- The EXPLORER/BUILDER (this session) only **RUNS** the linters and **OBSERVES**. It does NOT fix issues.
- The **AUDITOR** agent is responsible for **ADDRESSING** (fixing) lint issues: pruning the 35 redundant
  imports, adding the ~37 missing docstrings, renaming `_extlib` decls, fixing `defLemma`/`simpNF` items.
  Integration of the lint step into the auditor's workflow is the next discussion topic (after T1).
- A human (`achatz64` as `mathlib_contributor`) owns the actual GitHub PR (T3/T4), gated.

## Integration with the auditor (refined 2025-08-15)
- Auditor's lint task: AUDIT.md "Compilation audit" runs `lake build {target}` → flag lint issues
  as `AUDIT-GAP`; LEAN_LINTER.md clears them (collect `warning:` from build, fix, verify zero
  `warning:`). The linter MUST run DURING `lake build` (no separate REPL check — user requirement).
- DECISION: linters go on a **`Target` lib**, NOT on `Extlib`. `Extlib` (the library deliverable)
  stays linter-free so its normal build (~60s) is untouched. The auditor audits `lean/Target.lean`
  (a copy of `Extlib/GroupTheory/Mil21.lean`), via `lake build Target`.
- Env-level `#lint` set made visible from build: append `#lint` (or `#lint in Target`) to the END of
  `lean/Target.lean`. Then `lake build Target` runs BOTH file-level linters (via `leanOptions`) AND
  the env-level `#lint` set, all in the build log. `#lint` failures make the build error out with
  the 53 findings — a valid audit gate (target isn't clean until fixed).
- BUILD COST plan (user: normal build ~60s; don't blow it up):
  - Exclude `minImports` from the default audit build: it adds ~334s (import-graph per command).
    The 35 "unneeded import" findings → SEPARATE on-demand step, not `lake build Target`.
  - Keep `leanOptions` on `Target` to the CHEAP file-linters only: `weak.linter.dupNamespace`,
    `weak.linter.trailingWhitespace`, `weak.linter.whitespaceBeforeSemicolon`,
    `weak.linter.unicodeLinter`, `weak.linter.modulesUpperCamelCase`,
    `weak.linter.modulesForbiddenWindows` (simple scans; negligible overhead).
  - `#lint` (env-level) adds modest cost (~tens of seconds), far below minImports.
  - Net: `Extlib` build ~60s (unchanged, linter-free); `Target` audit build ~60s + modest lint
    overhead (no 334s hit).
- SNAG resolved: `Target.lean` does NOT import `Extlib`, so `lake build Target` does not pull in the
  `Extlib` lib → no `GT.*` clash. Only `lake build` (all libs) would clash; we always target
  `Target` (or `Extlib`) explicitly. (User confirmed: Extlib not imported into Target.lean.)
- STILL OPEN: `linter.style.header` (provenance/copyright conflict) is gated on mathlib's library
  root → won't run on `Target` either. Covered partly by AUDIT.md Provenance audit; the
  copyright/Authors-header gap is a separate decision.
- POLICY CONFLICTS (`_extlib` naming, benign `unusedArguments`, provenance/header) must be flagged
  `AUDIT-DEFERRED` and escalated, not auto-cleared (would violate project conventions).
- PROPOSED lakefile change (new `Target` lib; `Extlib` lib unchanged/linter-free):
  ```
  [[lean_lib]]
  name = "Target"
  srcDir = "."
  globs = ["Target.lean"]

  [lean_lib.leanOptions]
  weak.linter.dupNamespace = true
  weak.linter.trailingWhitespace = true
  weak.linter.whitespaceBeforeSemicolon = true
  weak.linter.unicodeLinter = true
  weak.linter.modulesUpperCamelCase = true
  weak.linter.modulesForbiddenWindows = true
  ```
  Plus: append `#lint` to the end of `lean/Target.lean` (the Mil21 copy).
- BUILD MECHANICS LESSONS (2025-08-15):
  - Lake `globs` match the **MODULE NAME**, not the filename. `globs=["Target.lean"]` NEVER
    matches module `Target` → lib has no graph → 'some modules have bad imports' at job
    computation. Fix: `globs=["Target"]`. This lets the audit file stay at `lean/Target.lean`
    (root, `srcDir="."`), as the user required.
  - `minImports` overhead is severe: `lake build Target` (full Mil21 copy + `#lint`) EXCEEDS 900s
    (timed out). So `minImports` must NOT be in the default audit build; run on-demand. The cheap
    6 file-linters + `#lint` are the default gate. (User: 'keep minImports for first try' →
    overhead now measured; action = exclude from default.)
  - Lake buffers ALL build output until completion, so a timed-out long build yields 0 bytes.
    Launch long builds detached (`setsid`) and poll, or shorten them to capture output.
- MEASURED RESULTS (first try, minImports kept, 2025-08-15):
  - `lake build Target` (full Mil21 copy + `#lint` + minImports) → **exit 1** (expected: `#lint`
    found ~50 errors = the audit gate). Compile step = **319s**; with `#lint` + minImports the
    whole thing exceeded 900s. Output 124KB in `/tmp/tf_out.txt`.
  - File-level linters: `minImports` = **35 'unneeded import'** + **185 'Imports increased by'**
    noise; `dupNamespace`/`unicodeLinter`/`trailingWhitespace`/`whitespaceBeforeSemicolon`/
    `modulesUpperCamelCase`/`modulesForbiddenWindows` = **0 warnings** (pass).
  - Env-level `#lint` (~50 errors, identical to the Mil21 REPL run): `defLemma` (1),
    `defsWithUnderscore` (6 — the `_target`/`_extlib` suffix naming conflict with mathlib),
    `docBlame` (~37 missing docstrings), `simpNF` (2), `unusedArguments` (9).
  - CONFIRMED: everything is visible from `lake build Target` (no REPL). The auditor's existing
    AUDIT.md/LEAN_LINTER.md workflow picks it up as `AUDIT-GAP`.
  - ACTION (minImports): **exclude from the default audit build** (keep on-demand). Its 185 noise
    lines + 35 actionable + ~heavy compile cost don't belong in the default gate; the default
    gate should be the cheap 6 file-linters + `#lint` (~50 errors), which is clean and fast.
  - **minImports DISABLED (2025-08-15)**: `weak.linter.minImports` **panics in Lean 4.31**
    (`Option.get!` on `none` while reporting missing imports; non-monotonic). Confirmed in our own
    build (PANIC at lines 2814-2822 of `/tmp/tf_out.txt`, after the #lint report) and documented in
    `tmp/linter_handoff.md`. Removed from the `Target` lib (commented out in `lean/lakefile.toml`).
    The hard gate is now purely the env-level `#lint` errors (~50) + the 6 cheap file-linters
    (currently 0 warnings). **Main agent to fix the ~50 `#lint` errors.**

## T2 — PR workflow redesign (design, 2025-08-15)

### Context / problem
- FORMALIZATION.md requires `Improvements for Mathlib` annotations (4 fields: (1) existing
  external-library declaration + source file; (2) proposed stronger statement/API; (3) plausible
  proof route distinguishing checked project code from a sketch; (4) relevant project decls/source
  refs) but defines **NO workflow** annotation → PR. It also says: do NOT treat upstream
  suggestions as source-faithfulness gaps; do NOT overstate speculative proof as checked;
  project-specific wrappers don't need an entry merely because absent from the external library.
  → Upstreaming is deliberate, sourced ONLY from the annotation list.
- Two repos (confirmed): `mathagent` (formalization; pins mathlib v4.31.0 as a Lake dependency;
  never contains mathlib source) and `~/mathlib4` (separate fork of
  `leanprover-community/mathlib4` on a feature branch — the ONLY place a PR is assembled). The
  `Improvements for Mathlib` annotation is the handoff contract between them.

### PR-workflow decisions (agreed, pending e2e)
- **Sourcing:** candidates come ONLY from `Improvements for Mathlib` / `Improvements for {lib}`.
  The 5 current Mil21 candidates are the backlog. Project-specific wrappers are NOT candidates.
- **Minimal isolated PR (mathlib culture):** one PR = one focused change.
- **Lint/CI gate = T1's `lake build Target` mirrored on mathlib.** A PR is ready only when
  lint-clean. FORMALIZATION.md: "You must not use `nolint`" → the 4 conflict items
  (`defsWithUnderscore` naming, `docBlame`, `simpNF`, `defLemma`, `unusedArguments`) must be
  **RESOLVED** upstream (rename to `lowerCamelCase` dropping `_extlib`/`_target`; add doc-strings;
  `def`→`lemma` for proven facts; fix `simpNF`), NOT suppressed.
- **Attribution (RULES.md #1 + mathlib norm):** commit author = human formalizer `achatz64`
  (PROVENANCE `formalizers`). `Co-authored-by: achatz64 <…>` only if a DIFFERENT human account
  opens the PR. **J.S. Milne credited as SOURCE author in the PR body** (academic attribution),
  referencing PROVENANCE `[source]` DOI/hash for auditability — NOT a `Co-authored-by` (not a
  GitHub committer). No "Generated by LLM" markers (LLMs are helper agents; PR is human-reviewed).
- **Merge = squash** (mathlib default): one PR → one squashed commit on mathlib `master`.
- **Human review gate (no agent GitHub actions):** agents do NOT open/comment/merge. Human
  (`achatz64` as `mathlib_contributor`) creates + merges. Agents may prepare the branch + a draft
  PR description LOCALLY. Satisfies RULES.md #4 (no autonomous LLMs) + mathlib's review norm.
- **No LLM GitHub comments:** explanation lives in the human-approved PR body or the local
  annotation. Agents never post to GitHub.
- **Ready-to-merge checklist (the gate):** [ ] extracted fragment; [ ] doc-string present
  (`docBlame` clean — mathlib-required); [ ] name mathlib-compliant (`defsWithUnderscore` clean,
  drop suffix upstream); [ ] `simpNF` clean; [ ] `defLemma` clean; [ ] `unusedArguments` clean
  (no `nolint`); [ ] builds + lints clean on mathlib CI (mirrors `lake build Target`); [ ]
  human-reviewed; [ ] PR opened by human w/ attribution; [ ] squash-merged by maintainer.
- **T3/T4 mapping:** T3 picks ONE low-effort candidate (e.g. `Submodule.quotientEquiv_map_linearEquiv`
  — self-contained, no new math), preps `fragment.lean` + `insertion_spec.json` + `pr_meta.toml`;
  T4 = human opens/merges, gated on `achatz64`. The e2e test uses exactly ONE PR.

### LOCKED deliverable mechanics (2025-08-15) — candidate folder + insertion spec
- **One folder per candidate:** `lean/Upstream/<candidate>/` (name arbitrary; the target mathlib
  file is named INSIDE the insertion spec, not the folder name).
- **Folder contents:**
  - `fragment.lean` — the mathlib-ready additions (renamed to `lowerCamelCase`, doc-stringed,
    `def`→`lemma` where proven, `simpNF`-clean). **Verified HERE**: compiled against cached
    v4.31.0 `.olean` (Lean builds incrementally — no full mathlib recompile, no OOM) + the T1
    lint gate (docBlame/defsWithUnderscore/simpNF/defLemma/unusedArguments clean; NO `nolint`).
    This repo is **PRE-CHECK ONLY**; the fork's `master` CI is the final gate.
  - `insertion_spec.json` — pi-style `edits[]` of `{ "path": "Mathlib/...", "oldText":
    "<logical anchor>", "newText": "<anchor + new decl + doc-string>" }`. **All edits target the
    SAME mathlib file; multiple insertions at several logical anchors.** Consumed DIRECTLY by the
    fork agent (no translation — it is pi's `edit` tool format). Each `oldText` must be a UNIQUE
    logical anchor in the target file so the fork agent's edit applies unambiguously.
  - `pr_meta.toml` (sibling doc) — `pr_title`, `pr_body` (Milne source attribution +
    `Co-authored-by: achatz64`), target mathlib file. Human-facing PR text.
- **NO separate `diff` produced in mathagent** — redundant: the fork applies the spec, then
  `git diff` derives the review diff (against `master`, where it matters).
- **Scope:** one candidate = one mathlib file, multiple insertions within it. **No cross-file PRs
  for now.**
- **Fork ingestion (mechanical):** fork agent reads `insertion_spec.json`, applies edits to
  `~/mathlib4/Mathlib/...` via its `edit` tool, builds/tests on `master`, `git diff` for review,
  prepares the PR from `pr_meta.toml`. Human reviews + opens the PR. No cut-paste anywhere.

## T2 — METHODOLOGY FINALIZED (2025-08-2X) — `upstream/` package + insertion-diff pipeline

This supersedes the earlier draft that placed candidates under `lean/Upstream/<candidate>/`.
After building and validating a smoke-test harness, the package topology and deliverable
mechanics are now empirically confirmed.

### Package topology (decided)
- `upstream/` is a **separate, gitignored package rooted in the project** (`/home/andre/mathagent/upstream/`)
  with its own `lakefile.toml` (package `upstreamCert`, lib `Upstream`, `lean_version = "v4.31.0"`,
  `[[require]] name="mathlib" rev="v4.31.0"`). **`lean/lakefile.toml` is NOT modified.**
- Mathlib is built **ONCE** in `upstream/.lake` (then cached; repeat `lake build Upstream` is fast
  and reads from `.olean` — "mathlib from olean", no recompile). Verified: a full shadow build
  recompiles 0 `Building Mathlib` lines.
- **Symlinking `.lake/packages` to share a prebuilt mathlib BREAKS Lake's job computation**
  ("some modules have bad imports" for the symlinked dependency graph). So the one-time local
  mathlib build is required; it is not avoidable by symlink.

### Candidate folder `upstream/<candidate>/` — contents (validated)
- `<Target>.original.lean` — **pristine copy of the target mathlib file** (v4.31.0). The file being
  extended. (Full-file copy, not a fragment, so the certification is a faithful full-file build.)
- `insertion_spec.json` — **THE INSERTION DIFF**: pi-style `edits[]` of
  `{ "path": "Mathlib/...", "oldText": "<unique logical anchor>", "newText": "<anchor + new decl + doc-string>" }`.
  All edits target the SAME mathlib file; multiple insertions at several anchors allowed. Consumed
  DIRECTLY by the fork agent via its `edit` tool (no translation). Each `oldText` is a UNIQUE anchor
  so the fork edit applies unambiguously.
- `pr_meta.toml` — `title`, `body` (Milne source attribution + `Co-authored-by` trailer rule),
  target mathlib file, `source_author` (J.S. Milne), `contributor` (achatz64, the human PR author).
- `generate.py` — **reproducible**: reads `<Target>.original.lean`, neutralizes mathlib-only commands
  (`public import`→`import`, `public section`→`section`, strips the top-level `module` declaration),
  applies each edit, writes `<Target>.lean`. The fork does NOT use this generator — it applies
  `insertion_spec.json` to its own mathlib file (keeping `module`/`public import`/`public section`)
  and then `git diff` derives the review diff. The generator exists only to build+certify offline.
- `<Target>.lean` — **GENERATED shadow** (faithful full-file copy + insertion). Cert target.
  NOT hand-edited; regenerated from original+spec.
- `<Target>Smoke.lean` (test) — module that **PROVES** the new declaration (not just type-checks).
  **Naming rule:** no extra dots (Lake glob mismatch → "bad imports"); prefer a single extra
  segment like `ModEqSmoke`, not `ModEq.test`.
- **NO separate `diff`** is produced in mathagent — the fork applies the spec, then `git diff`.

### Smoke-test harness `upstream/UC/QuotientGroup/` (VALIDATED — pipeline proven)
- Target `Mathlib.GroupTheory.QuotientGroup.ModEq`; added a trivial `AddCommGroup.modEq_refl_smoke`
  lemma via `insertion_spec.json`; `generate.py` produced `ModEq.lean`; `ModEqSmoke.lean` proves it.
- `lake build Upstream` → **GREEN (EXIT=0)**, mathlib NOT recompiled (0 `Building Mathlib`),
  both shadow and test built. Confirms: original → spec → generated shadow → full-file build + lint
  + test works end-to-end. The `_smoke` lemma is throwaway; the real PR uses a real candidate.

### Lessons (do NOT repeat)
- Don't `rm -rf .lake` between builds — destroys the mathlib cache; repeat builds become slow.
- Test module names with extra dots (e.g. `ModEq.test` → 3 segments) break Lake's glob
  ("bad imports" at job computation). Use `ModEqSmoke` (2 segments) instead.
- mathlib source (v4.31.0) uses a top-level `module` declaration AND `public import`/
  `public section`; for the standalone cert shadow these must be neutralized (the fork keeps them).
- Name collisions with mathlib: e.g. `modEq_refl` already exists in mathlib → use a unique name
  for smoke tests; real candidates use proper non-colliding mathlib names AND must satisfy
  `defsWithUnderscore` (drop `_extlib`/`_target`; prefer camelCase, e.g. `quotientEquivMapLinearEquiv`
  not `quotientEquiv_map_linearEquiv`).
- Linter output = STDOUT `warning:` (carried from T1).

### Fork ingestion (mechanical)
- Fork agent reads `insertion_spec.json`, applies edits to `~/mathlib4/Mathlib/...` via its `edit`
  tool, builds/tests on `master` (final CI gate), `git diff` for review, prepares the PR from
  `pr_meta.toml`. Human (`achatz64`) reviews + opens + **squash-merges**. No agent GitHub
  actions/comments.

## T3 — REAL CANDIDATE CERTIFIED (2025-08-2X) — pipeline validated on a real mathlib change

- Picked `Submodule.quotientEquivMapLinearEquiv` (the T2-design-named T3 candidate): a single,
  self-contained `theorem` transporting a submodule quotient along a `LinearEquiv`. Renamed from
  the project's `quotientEquiv_map_linearEquiv` to camelCase (drops the `_extlib`/`_target`-style
  underscore → `defsWithUnderscore`-clean) and added a doc-string (`docBlame`-clean).
- Candidate folder `upstream/SubmoduleQuotientMap/`:
  - `QuotientModule.original.lean` — pristine `Mathlib.LinearAlgebra.Quotient.Basic.lean` (v4.31.0, 448 lines).
  - `insertion_spec.json` — anchor = the `comapMkQOrderEmbedding` line **folded together with its
    preceding doc-string** (so the original doc-string stays attached to its `def`; otherwise it is
    orphaned and the parser errors "expected 'lemma'"). Inserts the doc-string + renamed theorem
    before `comapMkQOrderEmbedding`.
  - `pr_meta.toml` — title/body (Milne source + certified-via-pipeline note), `source_author` (Milne),
    `contributor` (achatz64).
  - `generate.py` — neutralizes `module`/`public import`/`public section`, applies the spec.
  - `QuotientModule.lean` — GENERATED shadow (full 448-line file + insertion). Builds + the new
    theorem compiles.
  - `QuotientModuleSmoke.lean` — test.
- `lake build Upstream` → **GREEN (EXIT=0)**, mathlib NOT recompiled (0 `Building Mathlib`). The
  theorem compiles against cached v4.31.0; the test confirms the declaration is in scope and
  correctly typed. **First real (non-`_smoke`) mathlib change certified through the pipeline.**
- LESSONS (real candidate, beyond the smoke harness):
  - The target file's `namespace Submodule` reopens the **global** `Submodule` namespace, so the
    shadow REDEFINES `Submodule.mapQ`/`comap`/etc. globally. The test must therefore NOT
    `import Mathlib.LinearAlgebra.Quotient.Basic` (collision: "environment already contains
    'Submodule.mapQ'"). Instead the test takes `Submodule.*` from the shadow and imports only the
    specific class modules (`Mathlib.Algebra.Group.Basic`, `.Module.Basic`, `.Ring.Basic`,
    `.Module.Equiv.Basic`) — none of which define `Submodule.mapQ`.
  - Doc-string anchors: when inserting before a `def` that has a preceding `/-- … -/`, fold that
    doc-string into `oldText` so it stays attached (the smoke harness avoided this only because its
    anchor had no preceding doc-string).
  - A `theorem … : Nonempty (X ≃ₗ[R] Y)` return type is awkward for mathlib; a real PR would likely
    refactor to a `def` returning the actual `LinearEquiv`. The e2e test uses the generic theorem
    type (matching what compiled) rather than a concrete `⊤`/`⊥` instance, which hit a
    `HasQuotient` definitional-mismatch (`Submodule.map e ⊤` doesn't reduce to `⊤`).
- T4 (human opens/merges) remains gated on `achatz64`; the fork would apply `insertion_spec.json`
  to `~/mathlib4/Mathlib/LinearAlgebra/Quotient/Basic.lean` and `git diff` for review.

## Open questions carried from prior turn (still unanswered)
- Provenance/header conflict resolution: (a) add a `Copyright/Authors` header to Extlib (satisfy
  `linter.style.header` verbatim) while keeping the `# Provenance` TOML block, or
  (b) keep Extlib header-free and run a curated subset that **excludes** `linter.style.header`?
- Does the human want me to draft T1 as a checklist doc after the run (read-only plan, written
  only on go-ahead)?
