/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
public import QPainleve.AlgebraicGeometry.Curves.Node.Order
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Total transform at a node

Blowing up a closed node of a Cartier divisor in a smooth integral surface gives its
scheme-theoretic strict transform and two copies of the exceptional divisor. The multiplicity
comes from the intrinsic singular locus, so this applies to self-nodes of an integral curve.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The total transform of a nodal Cartier divisor under the blowup at a closed node is its
strict transform plus twice the exceptional divisor, as an equality of ideal sheaves. -/
theorem totalTransform_eq_strictTransform_mul_sq_of_node
    {k : Type u} [Field k] {C X : Scheme.{u}} [X.Over (Spec (.of k))]
    [C.Over (Spec (.of k))] [IsIntegral X] (i : C ⟶ X) [i.IsOver (Spec (.of k))]
    [IsClosedImmersion i] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (hi : i.ker.IsEffectiveCartier) (hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)))
    (p : C) (hp : IsClosed ({i p} : Set X))
    (hnode : letI := hnodal.syntomic; p ∈ (C.singularLocus k).support) :
    let I := IdealSheafData.vanishingIdeal (Closeds.mk (closure {i p}) isClosed_closure)
    i.ker.comap I.blowupToBase =
      (I.blowupMap i.ker.subschemeι).ker * (I.comap I.blowupToBase) ^ 2 := by
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) (i p)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (X ↘ Spec (.of k)) 2).mp inferInstance).2 (i p) hp
  simpa only [i.stalkOrder_eq_two_of_node hi hnodal p hnode, ENat.toNat_ofNat] using
    hi.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim

end AlgebraicGeometry.Scheme.Hom
