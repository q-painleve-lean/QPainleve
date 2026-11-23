/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.AlgebraicGeometry.Curves.Node.Order

import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Strict and total transforms at nodes

Away from the center, the strict transform has the same nodes as the original boundary.

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

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- Outside the center, the strict transform has a node exactly over a node of the
original reduced boundary. -/
theorem isNodeOfReducedBoundary_ker_blowupMap_iff_of_notMem_support
    [IsLocallyNoetherian X] (I D : X.IdealSheafData) (s : X ⟶ S) {z : I.blowup}
    (hz : I.blowupToBase z ∉ I.support) :
    (I.blowupMap D.subschemeι).ker.IsNodeOfReducedBoundary (I.blowupToBase ≫ s) z ↔
      D.IsNodeOfReducedBoundary s (I.blowupToBase z) := by
  let U : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
  have hz' : I.blowupToBase z ∈ I.support.compl := by
    simpa only [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff] using hz
  let w : U := ⟨z, by
    simpa only [U, compl_support_comap, Scheme.Hom.mem_preimage] using hz'⟩
  have : IsOpenImmersion (U.ι ≫ I.blowupToBase) := by
    dsimp only [U]
    rw [compl_support_comap, ← morphismRestrict_ι]
    infer_instance
  have hstrict := isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    (I.blowupMap D.subschemeι).ker (I.blowupToBase ≫ s) U.ι w
  rw [comap_ker_blowupMap_subschemeι_exceptionalCompl I D, ← comap_comp] at hstrict
  have htotal := D.isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    s (U.ι ≫ I.blowupToBase) w
  have hleft : U.ι w = z := rfl
  have hright : (U.ι ≫ I.blowupToBase) w = I.blowupToBase z :=
    (Scheme.Hom.comp_apply _ _ _).trans (congrArg I.blowupToBase hleft)
  have h := hstrict.symm.trans htotal
  rwa [hleft, hright] at h

end AlgebraicGeometry.Scheme.IdealSheafData
