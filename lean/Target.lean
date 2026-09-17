import Extlib.GroupTheory.Mil21
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
# Provenance

```toml
[source]
title    = "Fields and Galois Theory (v5.00)"
author   = ["Milne, James S."]
location = "https://www.jmilne.org/math/CourseNotes/FT500.zip"
hash     = "sha256:4912e7f765eb63f8f255277dbdeddb168c31119ac6607a2b8bf8238e3358f472"
year     = 2021
type     = "book"

[formalization]
formalizers = ["achatz64"]
scope       = """
  Exercises, solutions, and material of purely expositional nature (remarks,
  examples, asides, notes) are omitted.  The stable TeX labels are recorded in
  comments.  Declaration names follow Mathlib conventions and deliberately
  state the Mathlib formulation, which is occasionally more general than the
  formulation in the text.
  """
source-hooks = ["labels"]
```
-/

/-!
# Fields and Galois Theory (Milne FT v5.00)

Formalization of Milne's *Fields and Galois Theory* (v5.00).  Source-extraction
script: `tools/ft_inventory.py`; coverage audit: `tools/ft_coverage.py`.
-/

namespace FT

/-!
## Basic Definitions and Results
-/

section Fields

/-- FT `ef1`. A nonzero commutative ring `R` is a field if and only if it has no
ideals other than `(0)` and `R`. -/
theorem isField_iff_forall_ideal_eq_bot_or_eq_top {R : Type*} [CommRing R] [Nontrivial R] :
    IsField R ↔ ∀ I : Ideal R, I = ⊥ ∨ I = ⊤ :=
  ⟨fun h I => (Ring.isField_iff_isSimpleOrder_ideal.mp h).eq_bot_or_eq_top I, fun H => by
    by_contra h
    obtain ⟨I, hI, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp h
    rcases H I with hIBot | hITop
    · exact hI.ne' hIBot
    · exact hItop.ne hITop⟩

/-- FT `ef14`. Let `R` be an integral domain containing a subfield `F` (as a subring).
If `R` is finite-dimensional as an `F`-vector space, then it is a field. -/
theorem isField_of_isDomain_of_finiteDimensional (F R : Type*) [Field F] [CommRing R] [IsDomain R]
    [Algebra F R] [FiniteDimensional F R] : IsField R :=
  IsField.of_isDomain_of_finite F R

end Fields

end FT
