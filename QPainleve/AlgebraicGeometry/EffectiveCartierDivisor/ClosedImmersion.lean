/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Closed integral curves as effective Cartier divisors

The ideal of a closed integral curve on a regular integral surface is effective
Cartier. The dimension formula identifies the image of the generic point as a
codimension-one point, and reducedness identifies the ideal of the immersion
with the vanishing ideal of that point's closure.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An integral closed curve on a regular integral surface over a field is an
effective Cartier divisor, with the ideal of the given closed immersion. -/
public theorem isEffectiveCartier_ker_of_isRegular_of_dim_eq_two
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] [IsRegular X] (hX : topologicalKrullDim X = 2)
    (hC : topologicalKrullDim C = 1) : i.ker.IsEffectiveCartier := by
  rw [i.ker_eq_vanishingIdeal_closure_genericPoint]
  exact IdealSheafData.isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular
    (fun x ↦ WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim x).trans_eq hX))
    (i.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC)

end AlgebraicGeometry.Scheme.Hom
