/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

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

/-- The ideal of a closed integral subscheme is the vanishing ideal of the closure of the
image of its generic point. -/
public theorem ker_eq_vanishingIdeal_closure_genericPoint {C X : Scheme.{u}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] :
    i.ker = IdealSheafData.vanishingIdeal
      ⟨closure {i (genericPoint C)}, isClosed_closure⟩ := by
  have hp := (genericPoint_spec C).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at hp
  have hs : i.ker.support = ⟨closure {i (genericPoint C)}, isClosed_closure⟩ := by
    apply SetLike.coe_injective
    rw [i.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq, ← hp]
    rfl
  have : IsReduced i.ker.subscheme := isReduced_of_isOpenImmersion (CategoryTheory.inv i.toImage)
  have hi := (IdealSheafData.isReduced_subscheme_iff_radical_eq i.ker).mp ‹_›
  rw [← hi, ← IdealSheafData.vanishingIdeal_support, hs]

/-- The generic point of a closed integral curve on an irreducible surface of finite type
over a field maps to a point of codimension one. -/
public theorem coheight_apply_genericPoint_eq_one_of_dim_eq_two
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C]
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IrreducibleSpace X] (hX : topologicalKrullDim X = 2)
    (hC : topologicalKrullDim C = 1) : Order.coheight (i (genericPoint C)) = 1 := by
  have hp := (genericPoint_spec C).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at hp
  have hdim := coheight_add_height_eq_topologicalKrullDim k (i (genericPoint C))
  rw [height_eq_topologicalKrullDim_closure_singleton, hp,
    topologicalKrullDim_range_of_isPreimmersion, hC, hX] at hdim
  apply ENat.add_left_injective_of_ne_top (n := 1) (by simp)
  exact WithBot.coe_injective (by
    simpa only [WithBot.coe_add, WithBot.coe_one] using hdim.trans
      (by decide : (2 : WithBot ℕ∞) = 1 + 1))

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
