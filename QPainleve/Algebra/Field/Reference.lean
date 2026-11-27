/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.Analysis.Real.Cardinality

/-!
# A reference field for geometric comparison

The geometric proofs choose centers away from countably many closed conditions. An algebraic
closure of a rational function field with an uncountable set of variables supplies a field
for that choice and for specialization to other coefficient fields.
-/

@[expose] public section

namespace QPainleve

/-- An algebraically closed characteristic-zero field with uncountably many elements. -/
abbrev ReferenceField := AlgebraicClosure (FractionRing (MvPolynomial ℝ ℚ))

instance : Uncountable ReferenceField := by
  let F := FractionRing (MvPolynomial ℝ ℚ)
  let : Uncountable F :=
    ((IsFractionRing.injective (MvPolynomial ℝ ℚ) F).comp MvPolynomial.X_injective).uncountable
  exact (algebraMap F ReferenceField).injective.uncountable

end QPainleve
