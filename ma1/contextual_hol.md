# Contextual HOL to Core

This note defines a translation layer between ordinary HOL/FOL-looking
statements and Core.  The point is to stop hand-writing Core formulas in many
nearly equivalent shapes.  The translation target is a canonical `Pred` over a
right-nested context object.

The intended pipeline is:

```text
HOL statement
  -> contextual HOL judgment
  -> canonical Core predicate
```

The middle layer is essential.  A formula does not translate by itself; it
translates relative to an ordered context.

## From HOL to Contextual HOL

The elaboration step from HOL to contextual HOL is mechanical once the input
separates schema parameters from object variables.

Use this source shape for axioms and theorem schemas:

```text
schema p1 : P1, ..., pk : Pk
object x1 : X1, ..., xn : Xn
assume A1, ..., Am
show phi
```

The elaborated contextual sequent is:

```text
x1 : X1, ..., xn : Xn | A1, ..., Am |- phi
```

with the schema parameters recorded separately.  Schema parameters are not part
of the object context; they index the family of statements.

For a closed source formula with explicit object quantifiers:

```text
forall x:X. phi
```

elaboration may either keep the quantifier inside the formula or move it to the
object context when forming a theorem schema:

```text
object x : X
show phi
```

These are equivalent presentations at the HOL level.  The second form is often
the better authoring form for axioms because it makes object variables explicit
before Core translation.

### Elaboration Rules

Given a source signature, elaboration checks names and produces a contextual HOL
judgment.

1. Resolve every identifier in a term.

   * If it is in the object context, it is an object variable.
   * If it is in the schema telescope or global constants, it is a parameter or
     constant.
   * Otherwise elaboration fails.

2. Check relation atoms against the declared relation type.

   For a binary relation:

   ```text
   R : Pred (A × B)
   ```

   an atom `R(t,u)` is accepted only when `t : A` and `u : B`.

3. Elaborate connectives recursively in the same object context.

4. Elaborate object quantifiers by extending the object context at the head:

   ```text
   Gamma |- forall x:X. phi
   ```

   elaborates the body in:

   ```text
   x : X, Gamma
   ```

5. Elaborate assumptions and the conclusion in the same object context.

The output of this phase is not yet Core syntax.  It is a checked contextual HOL
sequent:

```text
schema params; Gamma | Delta |- phi
```

### Closing a Contextual Sequent

To export a contextual sequent as a closed Core proposition, first turn
assumptions into an implication chain over the current context:

```text
Delta = A1, ..., Am
body = A1 -> (A2 -> (... -> phi))
```

Then close the object context by object `Forall`.

Define:

```text
close([], P : Pred Final) = Pred.term P
close(x:X, Gamma, P : Pred (X × C[Gamma])) =
  close(Gamma, Forall X C[Gamma] P)
```

Example:

```text
schema b : Sets, z : Sets
object a : Sets
show a = b -> (a in z <-> b in z)
```

closes as:

```lean
Pred.term (Forall Sets Final
  (Pred.imply (Sets × Final)
    ...SetEq(a,b)...
    ...iff(a in z, b in z)...))
```

This is the mechanical reason `memCong_left_all` is binder-usable while a
pointwise Core head-parameter axiom is not.

### Implicit Free Variables

For design clarity, the preferred input has an explicit `object` block.  A tool
may support implicit free-variable closure, but it must choose a deterministic
order, for example first occurrence from left to right.  For repository axioms,
implicit object variables should be rejected or expanded before committing the
Core translation, because variable order changes the generated projection shape.

## Contexts

A context is an ordered list of object variables:

```text
Gamma = x0 : X0, x1 : X1, ..., xn : Xn
```

Core uses newest/innermost variable first.  The context object is:

```text
C[] = Final
C[x : X, Gamma] = X × C[Gamma]
```

So if the current object context is:

```text
x : X, y : Y
```

then the Core context object is:

```lean
X × (Y × Final)
```

The newest variable is read by `v0`, the next by `v1`, and so on.  These
projectors are only notation for `fst`/`snd` compositions; the translation does
not need infinitely many primitive beta rules for them.

## Judgments

Use two translation judgments:

```text
Gamma |- t : A      maps to    [[t]]Gamma : C[Gamma] -> A
Gamma |- phi : o    maps to    [[phi]]Gamma : Pred C[Gamma]
```

Closed formulas are the special case `Gamma = []`:

```text
[] |- phi : o
[[phi]][] : Pred Final
Pred.term ([[phi]][]) : PC
```

## Terms

Variables are projected out of the context.  Constants and schema parameters are
weakened into the context.

```text
[[x0]](x0:X0, Gamma) = v0 X0 C[Gamma]
[[x1]](x0:X0, x1:X1, Gamma) = v1 X0 X1 C[Gamma]
[[a]]Gamma = Cart.weakening A C[Gamma] a
```

For variables deeper than the available named `vN`, use the corresponding
`fst`/`snd` composition.  For example:

```lean
(fst Z Final) ∘ (snd Y (Z × Final)) ∘ (snd X (Y × (Z × Final)))
```

reads the third variable in context `X × (Y × (Z × Final))`.

## Formulas

Relation atoms are always translated through `sub2`.

```text
[[R(t, u)]]Gamma =
  sub2 C[Gamma] A B R [[t]]Gamma [[u]]Gamma
```

Connectives preserve the current context:

```text
[[phi /\ psi]]Gamma = Pred.and C[Gamma] [[phi]]Gamma [[psi]]Gamma
[[phi \/ psi]]Gamma = Pred.or C[Gamma] [[phi]]Gamma [[psi]]Gamma
[[phi -> psi]]Gamma = Pred.imply C[Gamma] [[phi]]Gamma [[psi]]Gamma
[[not phi]]Gamma    = Pred.not C[Gamma] [[phi]]Gamma
```

Quantifiers extend the object context:

```text
[[forall x:X. phi]]Gamma = Forall X C[Gamma] [[phi]](x:X, Gamma)
[[exists x:X. phi]]Gamma = Exist X C[Gamma] [[phi]](x:X, Gamma)
```

This is the central convention: object variables become object context entries
and object quantifiers.  They do not become Core head parameters merely because
that is convenient at the point where the axiom is stated.

## Schema Parameters vs Object Variables

Before translation, classify binders.

Object variables are variables of the object logic.  They are translated into
context entries and, when closed, into `Forall`/`Exist`.

Schema parameters index a family of statements.  They remain Core head
parameters.  Examples:

```text
phi : Pred Sets
R : Pred (X × X)
A : Sets
```

The rule is:

```text
Object variables go into Gamma.
Schema parameters stay in the Core telescope.
```

This avoids the pointwise axiom trap.  A statement like:

```text
forall a. a = b -> (a in z <-> b in z)
```

should be encoded with object `a` under `Forall`, while `b` and `z` may remain
schema/head parameters if they are fixed for the axiom family.

## Weakening and Substitution

Every formula lives over a specific context.  Moving a formula to a larger
context is weakening/reindexing, not textual reuse.

If `sigma : C[Delta] -> C[Gamma]`, then:

```text
[[phi[sigma]]]Delta = [[phi]]Gamma ∘ sigma
```

The Core beta-basis should make this observationally true at `PC`, because Core
does not have equality at arbitrary type.

## Adequacy Theorems

These are the theorems that justify the translation. Current status is noted per
item; all Lean names below live in `formalization/ContextualHOL/`.

1. Formula adequacy. **(planned)**

   For every HOL formula `phi` with free object variables in `Gamma`, erasing the
   contextual translation gives back `phi`, up to alpha-renaming and ordinary
   HOL beta/eta equivalence.

   Not yet a Lean theorem. The translation itself is realized (`Syntax`, `Elab`,
   `Core`, `CorePrinter`), so an erasure/round-trip statement can be stated
   against it, but no `adequacy`/`erase` lemma exists yet.

2. Proof lifting. **(proved — M3.3)**

   If ordinary HOL proves:

   ```text
   A1, ..., An |- phi
   ```

   with free object variables in `Gamma`, then contextual HOL proves:

   ```text
   Gamma | [[A1]]Gamma, ..., [[An]]Gamma |- [[phi]]Gamma
   ```

   This is `proves_lift` in `ProvesLift.lean`: `Proves env Γ Δ phi` implies a
   `CoreThm (SeqLift ...)` over the lifted assumptions and conclusion, discharged
   by induction on the `Proves` derivation. The per-connective lifting lemmas
   (`liftImp_some`, `liftAnd_some`, …) and the chain combinators in `Lifting.lean`
   (`chainHyp`, `chainMP`, `chainIffMp`, …) are the supporting infrastructure.

3. Proof erasure. **(planned)**

   If contextual HOL proves:

   ```text
   Gamma | Delta |- phi
   ```

   then ordinary HOL proves the erased sequent.

   The converse direction to (2); not yet formalized.

4. Structurality. **(machinery proved)**

   Proofs are stable under context maps:

   ```text
   Gamma | Delta |- phi
   sigma : C[Theta] -> C[Gamma]
   --------------------------------
   Theta | Delta[sigma] |- phi[sigma]
   ```

   The substitution/weakening core is proved: `substEquiv_sound` (and its closed
   form `substEquiv_sound_closed`) in `SubstSound.lean`, with `Weakening.lean` for
   the reindexing lemmas. `proves_lift` already consumes this via `substIffLift` /
   `weakenIff` to move lifted axioms under binders. A standalone structurality
   theorem over the `Proves` judgment is not separately stated.

## Axiom Translation Policy

An axiom schema should be normalized before Core translation:

```text
Pi schema parameters. forall object variables. body
```

Translate schema parameters as Core head parameters.  Translate object variables
with object `Forall` and the formula translation above.

Bad-for-binders shape:

```lean
axiom memCong_left (a b z : Sets) : ...
```

Canonical object-level shape:

```lean
axiom memCong_left_all (b z : Sets) :
  Pred.term (Forall Sets Final (memCongBody b z))
```

The latter can be consumed under binders because the varying object `a` is an
object variable, not only a named Core head parameter.

## Translation Examples

Atomic relation with one variable and one parameter:

```text
Gamma = x : X
R(x, a)
```

```lean
sub2 (X × Final) X X R
  (v0 X Final)
  (Cart.weakening X (X × Final) a)
```

Closed universal:

```text
forall x:X. R(x, a)
```

```lean
Pred.term (Forall X Final
  (sub2 (X × Final) X X R
    (v0 X Final)
    (Cart.weakening X (X × Final) a)))
```

Nested universal:

```text
forall y:Y. forall x:X. R(x, y)
```

```lean
Pred.term (Forall Y Final
  (Forall X (Y × Final)
    (sub2 (X × (Y × Final)) X Y R
      (v0 X (Y × Final))
      (v1 X Y Final))))
```

Clean existential body:

```text
exists w:X. R(w, A) /\ R(z, w)
```

```lean
Pred.term (Exist X Final
  (Pred.and (X × Final)
    (sub2 (X × Final) X X R
      (v0 X Final)
      (Cart.weakening X (X × Final) A))
    (sub2 (X × Final) X X R
      (Cart.weakening X (X × Final) z)
      (v0 X Final))))
```

## Tooling

The translator was built in **Lean**, not as the originally-planned standalone
JSON-AST tool, and it goes well past "make the convention mechanical" — the same
`formalization/ContextualHOL/` project also carries the proof-lifting and
substitution-soundness theorems above.

The pipeline:

* `Syntax.lean` — typed AST: `Ty`, `Term`, `Formula`, `Sequent`, `Env` (the
  in-Lean replacement for the "typed JSON AST").
* `Elab.lean` — elaboration and the checks below, producing the contextual
  `CPred`/`CMap` translation.
* `Core.lean`, `CorePrinter.lean` — render the canonical Core text
  (`Cor.renderAxiom`, `Cor.renderFile`).
* `GenerateCoreExamples.lean` — the executable driver. Its `main` emits
  `ma1/generated_contextual_hol_examples.cor` from the example sequents
  (`reflexiveSeq`, `symmetricStepSeq`, `memCongSeq`, `sepSeq`).

The five originally-planned checks are all enforced by the elaborator:

1. Every variable occurrence is found in the object context.
2. Every constant/schema parameter has a declared type.
3. Relation atoms use declared relation arities and types.
4. Quantifiers extend the context by prepending the bound variable.
5. Output uses `sub2`, `Pred.*`, `Forall`, `Exist`, and `Cart.weakening` only.

The "linter that compares handwritten Core against the normal form" also exists,
as machine-checked diff files rather than a separate program:
`contextual_hol_regen_check.cor` ascribes each handwritten `set.cor` statement as
the *type* of the corresponding generated axiom instance, so the file type-checks
iff the translator reproduces the handwritten form definitionally.
`contextual_hol_basis_derivation_check.cor` does the analogous check against the
beta-basis derivations.

Beyond the original plan, the project also contains the proof-search and
finite-state layers (`Search.lean`, `Focused.lean`, `FiniteState.lean`) and the
certificate/evidence machinery (`Evidence.lean`, `SubstEvidenceBuilder.lean`),
which are downstream of this translation rather than part of it.
