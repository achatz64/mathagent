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

The target theorems are:

1. Formula adequacy.

   For every HOL formula `phi` with free object variables in `Gamma`, erasing the
   contextual translation gives back `phi`, up to alpha-renaming and ordinary
   HOL beta/eta equivalence.

2. Proof lifting.

   If ordinary HOL proves:

   ```text
   A1, ..., An |- phi
   ```

   with free object variables in `Gamma`, then contextual HOL proves:

   ```text
   Gamma | [[A1]]Gamma, ..., [[An]]Gamma |- [[phi]]Gamma
   ```

3. Proof erasure.

   If contextual HOL proves:

   ```text
   Gamma | Delta |- phi
   ```

   then ordinary HOL proves the erased sequent.

4. Structurality.

   Proofs are stable under context maps:

   ```text
   Gamma | Delta |- phi
   sigma : C[Theta] -> C[Gamma]
   --------------------------------
   Theta | Delta[sigma] |- phi[sigma]
   ```

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

## Tooling Plan

The first tool should be a small canonical translator from a typed JSON AST to
Core text.  It should not prove anything.  Its job is to make the convention
mechanical and testable.

Planned checks:

1. Every variable occurrence is found in the object context.
2. Every constant/schema parameter has a declared type.
3. Relation atoms use declared relation arities and types.
4. Quantifiers extend the context by prepending the bound variable.
5. Output uses `sub2`, `Pred.*`, `Forall`, `Exist`, and `Cart.weakening` only.

Later, a linter can compare handwritten Core formulas against this normal form.
