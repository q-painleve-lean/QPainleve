/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import QPainleve.AlgebraicGeometry.Curves.Node.Order
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.RingTheory.FittingIdeal.Basic

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Intersection
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.Intersection
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Strict and total transforms at nodes

Away from the center, the strict transform has the same nodes as the original boundary.

Blowing up a closed node of a Cartier divisor in a smooth integral surface gives its
scheme-theoretic strict transform and two copies of the exceptional divisor. The multiplicity
comes from the intrinsic singular locus, so this applies to self-nodes of an integral curve.

In the reduced total transform the exceptional curve meets the strict transform
transversely. At each attachment the first Fitting ideal of the differentials is
the maximal ideal, as in the nodal criterion of the
[Stacks Project, Lemma 53.19.7](https://stacks.math.columbia.edu/tag/0C4D).
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

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

/-- At each attachment point over the blown-up node, the first Fitting ideal
of the differentials of the reduced total transform is the maximal ideal.
The attachment is between a branch of the strict transform and the one
exceptional component. -/
theorem IsEffectiveCartier.fittingIdeal_stalk_reducedTotalTransform_of_node
    {k : Type u} [Field k] [PerfectField k] [X.Over (Spec (.of k))]
    [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
    {p : D.subscheme} (hp : (let := hnodal.syntomic; p ∈ (D.subscheme.singularLocus k).support))
    (hc : IsClosed ({D.subschemeι p} : Set X)) :
    let I := vanishingIdeal (Closeds.mk (closure {D.subschemeι p}) isClosed_closure)
    let π := I.blowupToBase
    let R := (D.comap π).radical
    let _ : I.blowup.Over (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    let _ : LocallyOfFiniteType (R.subscheme ↘ Spec (.of k)) := by
      rw [R.over_eq_subschemeι_comp]
      have : SmoothOfRelativeDimension 2 (π ≫ X ↘ Spec (.of k)) :=
        smoothOfRelativeDimension_blowup_closed_point (X ↘ Spec (.of k)) hc
      have : Smooth (π ≫ X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
      exact inferInstanceAs (LocallyOfFiniteType (R.subschemeι ≫ (π ≫ X ↘ Spec (.of k))))
    ∀ z : R.subscheme, R.subschemeι z ∈ ((I.blowupMap D.subschemeι).ker ⊔ I.comap π).support →
      let _ := R.subscheme.essFiniteType_stalk k z
      fittingIdeal (R.subscheme.presheaf.stalk z) Ω[R.subscheme.presheaf.stalk z⁄k] 1 =
        IsLocalRing.maximalIdeal (R.subscheme.presheaf.stalk z) := by
  let q := D.subschemeι p
  let I := vanishingIdeal (Closeds.mk (closure {q}) isClosed_closure)
  let π := I.blowupToBase
  let s := X ↘ Spec (.of k)
  let S := (I.blowupMap D.subschemeι).ker
  let E := I.comap π
  let : I.blowup.Over (Spec (.of k)) := ⟨π ≫ s⟩
  have : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point s hc
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have := isRegularLocalRing_stalk_of_smooth s q
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 q hc
  have : IsIntegral I.blowup := isIntegral_blowup_closed_point s hc
  have : Surjective π := surjective_blowupToBase_point hc hdim
  have : IsReduced E.subscheme :=
    @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hc)
  have : IsReduced D.subscheme := hnodal.isReduced
  have hI : (X.fromSpecResidueField q).ker = I := X.ker_fromSpecResidueField_eq_vanishingIdeal q
  have hDI : D ≤ I := hI ▸ (D.le_ker_fromSpecResidueField_iff_mem_support hc).mpr
    (D.range_subschemeι.le ⟨p, rfl⟩)
  have hR : (D.comap π).radical = S * E :=
    I.radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI
  have hS : S.IsEffectiveCartier :=
    (hD.exists_strictTransform_cartierDivisor (p := q) hc hdim
      (hD.comap_of_isDominant π)).choose
  have htrans :=
    stalkIdeal_sup_eq_maximalIdeal_strictTransform_exceptional D.subschemeι hnodal hp hc
  have : Smooth (I.blowup ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  -- Transport the statement with its stalk ring and base algebra along the ideal equality.
  let F (J : I.blowup.IdealSheafData) : Prop :=
    let _ : LocallyOfFiniteType (J.subscheme ↘ Spec (.of k)) := by
      rw [J.over_eq_subschemeι_comp]
      infer_instance
    ∀ z : J.subscheme, J.subschemeι z ∈ (S ⊔ E).support →
      let _ := J.subscheme.essFiniteType_stalk k z
      fittingIdeal (J.subscheme.presheaf.stalk z) Ω[J.subscheme.presheaf.stalk z⁄k] 1 =
        IsLocalRing.maximalIdeal (J.subscheme.presheaf.stalk z)
  have hfit : F (S * E) := by
    intro z hz
    have h := htrans ((S * E).subschemeι z) hz
    exact fittingIdeal_stalk_mul_eq_maximalIdeal_of_stalkIdeal_sup_eq (k := k) hS
      I.isEffectiveCartier_comap_blowupToBase z h.1 h.2
  exact (congrArg F hR).mpr hfit

end AlgebraicGeometry.Scheme.IdealSheafData
