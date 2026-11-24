/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Node

import TauCeti.RingTheory.Etale.Field
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Intersection
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.Transverse
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Scheme.ClosedPoint
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Nodality after a boundary-node blowup

The reduced total transform of a nodal Cartier divisor at a closed node is
nodal. Near the attachment points the strict and exceptional divisors meet
transversely, including when the original node is a self-node. The other
points are covered by the original curve off the center and by the smooth
exceptional line off the strict transform.
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem exists_nodal_neighbourhood_of_comap_eq
    {k : Type u} [Field k] {X Y U : Scheme.{u}}
    {D : X.IdealSheafData} {E : Y.IdealSheafData}
    {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)}
    (j : U ⟶ X) (i : U ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion i]
    (hbase : j ≫ s = i ≫ t) (hDE : D.comap j = E.comap i)
    (hE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (p : D.subscheme) (hp : D.subschemeι p ∈ Set.range j) :
    ∃ (W : Scheme.{u}) (g : W ⟶ D.subscheme), IsOpenImmersion g ∧ p ∈ Set.range g ∧
      AtWorstNodalOfRelativeDimensionOne (g ≫ D.subschemeι ≫ s) := by
  let g := subschemeMap (D.comap j) D j (le_map_comap _ _)
  let h := subschemeMap (E.comap i) E i (le_map_comap _ _)
  have hpb : IsPullback (D.comap j).subschemeι g j D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [g]) (by simp)
  have hpb' : IsPullback (E.comap i).subschemeι h i E.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [h]) (by simp)
  have : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb' inferInstance
  refine ⟨_, g, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd_of_isPullback hpb]
    exact hp
  · rw [← hpb.w_assoc, hbase, hDE, hpb'.w_assoc]
    exact hE.comp_of_etale h

/-- If a blowup center restricts to a Cartier divisor on a nodal boundary,
the strict transform is isomorphic to the original boundary over the base and is nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_strictTransform_of_isEffectiveCartier_comap
    {X Y : Scheme.{u}} {D I : X.IdealSheafData} (s : X ⟶ Y)
    (hD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hC : (I.comap D.subschemeι).IsEffectiveCartier) :
    AtWorstNodalOfRelativeDimensionOne
      ((I.blowupMap D.subschemeι).ker.subschemeι ≫ I.blowupToBase ≫ s) := by
  let g := I.blowupMap D.subschemeι
  let π := (I.comap D.subschemeι).blowupToBase
  have : IsIso π := (isIso_blowupToBase_iff _).mpr hC
  let e := IsClosedImmersion.lift g.ker.subschemeι g (ker_subschemeι _).le
  have : IsIso e := IsClosedImmersion.isIso_lift _ _ (ker_subschemeι _)
  have hcomp : e ≫ g.ker.subschemeι ≫ I.blowupToBase ≫ s = π ≫ D.subschemeι ≫ s := by
    rw [IsClosedImmersion.lift_fac_assoc, blowupMap_blowupToBase_assoc]
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @AtWorstNodalOfRelativeDimensionOne)
    e _).mp
  rw [hcomp]
  exact hD.comp_of_etale π

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "base" => (X ↘ Spec (CommRingCat.of k))

private theorem smoothOfRelativeDimension_exceptional {x : X}
    (hx : IsClosed ({x} : Set X)) :
    let I := vanishingIdeal (Closeds.mk (closure ({x} : Set X)) isClosed_closure)
    SmoothOfRelativeDimension 1
      ((I.comap I.blowupToBase).subschemeι ≫ I.blowupToBase ≫ base) := by
  dsimp only
  rw [← X.ker_fromSpecResidueField_eq_vanishingIdeal x]
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have := isRegularLocalRing_stalk_of_smooth base x
  have hdim :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp inferInstance).2 x hx
  obtain ⟨e, hpb, -, -⟩ :=
    exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint x hx hdim
  have := X.moduleFinite_residueField_of_isClosed (k := k) hx
  have : Algebra.Etale k (X.residueField x) := .of_isSeparable _ _
  let s := X.fromSpecResidueField x ≫ base
  have : Etale s := by
    dsimp only [s]
    rw [Scheme.fromSpecResidueField_comp_over]
    exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : SmoothOfRelativeDimension 0 s := inferInstance
  have hs : SmoothOfRelativeDimension 1
      ((projectiveLine (X.residueField x) ↘ Spec (.of (X.residueField x))) ≫ s) := by
    exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0)
      ((projectiveLine (X.residueField x) ↘ Spec (.of (X.residueField x))) ≫ s))
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    e.hom _).mp
  rw [← Category.assoc e.hom, hpb.w_assoc]
  exact hs

variable [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]

section

variable {D : X.IdealSheafData}
  (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k)))
  (hD : D.IsEffectiveCartier) {p : D.subscheme}
  (hp : IsClosed ({D.subschemeι p} : Set X))

local notation "x" => D.subschemeι p
local notation "I" => vanishingIdeal (Closeds.mk (closure ({x} : Set X)) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "E" => comap (I) (π)
local notation "S" => Scheme.Hom.ker (blowupMap (I) (subschemeι D))
local notation "R" => radical (D.comap (π))

include hnodal hD hp in
private theorem exists_nodal_neighbourhood_attachment
    {B : (I).blowup.IdealSheafData} (hB : B = (S) * (E)) (z : B.subscheme)
    (hnode : (D.subschemeι ≫ base).IsNodeAt p)
    (hz : B.subschemeι z ∈ ((S) ⊔ (E)).support) :
    ∃ (W : Scheme.{u}) (j : W ⟶ B.subscheme), IsOpenImmersion j ∧ z ∈ Set.range j ∧
      AtWorstNodalOfRelativeDimensionOne (j ≫ B.subschemeι ≫ (π) ≫ base) := by
  subst B
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType base
  have := isRegularLocalRing_stalk_of_smooth base (x)
  have hdim :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp inferInstance).2 _ hp
  let s := (π) ≫ base
  let : (I).blowup.Over (Spec (.of k)) := ⟨s⟩
  have : SmoothOfRelativeDimension 2 ((I).blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point base hp
  have : IsIntegral (I).blowup := isIntegral_blowup_closed_point base hp
  have : Surjective (π) := surjective_blowupToBase_point hp hdim
  have hS : (S).IsEffectiveCartier :=
    (hD.exists_strictTransform_cartierDivisor hp hdim (hD.comap_of_isDominant (π))).choose
  let : D.subscheme.Over (Spec (.of k)) := ⟨D.subschemeι ≫ base⟩
  have : SyntomicOfRelativeDimension 1 (D.subscheme ↘ Spec (.of k)) := hnodal.syntomic
  have hsing : p ∈ (D.subscheme.singularLocus k).support :=
    (D.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus p).mpr
      (((D.subschemeι ≫ base).isNodeAt_iff_notMem_smoothLocus hnodal p).mp hnode)
  have htrans := stalkIdeal_sup_eq_maximalIdeal_strictTransform_exceptional
    D.subschemeι hnodal hsing hp
  dsimp only [Closeds.closure] at htrans
  obtain ⟨hc, hsum⟩ := htrans _ hz
  have hs : (I).blowup ↘ Spec (.of k) = (π) ≫ base := rfl
  simpa only [hs, Category.assoc] using
    exists_nodal_neighbourhood_mul_of_stalkIdeal_sup_eq (k := k)
      hS (I).isEffectiveCartier_comap_blowupToBase z hc hsum

include hnodal hD hp in
private theorem exists_nodal_neighbourhood_radical_comap (z : (R).subscheme)
    (hnode : (D.subschemeι ≫ base).IsNodeAt p) :
    ∃ (W : Scheme.{u}) (j : W ⟶ (R).subscheme), IsOpenImmersion j ∧ z ∈ Set.range j ∧
      AtWorstNodalOfRelativeDimensionOne (j ≫ (R).subschemeι ≫ (π) ≫ base) := by
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian base
  have : IsReduced D.subscheme := hnodal.isReduced
  have := isRegularLocalRing_stalk_of_smooth base (x)
  have hdim :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp inferInstance).2 _ hp
  let y := (R).subschemeι z
  by_cases hy : y ∈ (E).support
  · have : IsReduced (E).subscheme :=
      @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hp)
    have hDI : D ≤ (I) :=
      ((D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr
        (D.range_subschemeι.le (Set.mem_range_self p))).trans
          (X.ker_fromSpecResidueField_eq_vanishingIdeal (x)).le
    have hR : (R) = (S) * (E) :=
      (I).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI
    by_cases hz : y ∈ (S).support
    · apply exists_nodal_neighbourhood_attachment hnodal hD hp hR z hnode
      rw [← SetLike.mem_coe, support_sup, Closeds.coe_inf]
      exact ⟨hz, hy⟩
    · let U : (I).blowup.Opens := (S).support.compl
      have hU : y ∈ U := hz
      have hS : (S).comap U.ι = ⊤ := (comap_eq_top_iff _ _).mpr (Scheme.Opens.ι_preimage_self _)
      have heq : (R).comap U.ι = (E).comap U.ι := by rw [hR, comap_mul, hS, top_mul]
      exact exists_nodal_neighbourhood_of_comap_eq U.ι U.ι rfl heq
        (by
          have := smoothOfRelativeDimension_exceptional (k := k) hp
          exact AtWorstNodalOfRelativeDimensionOne.of_smooth _) z ⟨⟨y, hU⟩, rfl⟩
  · let U : (I).blowup.Opens := (E).support.compl
    have : IsOpenImmersion (U.ι ≫ (π)) := by
      dsimp only [U]
      rw [compl_support_comap, ← morphismRestrict_ι]
      infer_instance
    have heq : (R).comap U.ι = D.comap (U.ι ≫ (π)) := by
      rw [← radical_comap_of_isOpenImmersion, ← comap_comp, radical_comap_of_isOpenImmersion,
        D.isReduced_subscheme_iff_radical_eq.mp inferInstance]
    exact exists_nodal_neighbourhood_of_comap_eq U.ι (U.ι ≫ (π))
      (by simp only [Category.assoc]) heq hnodal
      z ⟨⟨y, hy⟩, rfl⟩

include hnodal hD hp in
/-- Blowing up a closed node of a nodal Cartier divisor in a smooth surface gives a
nodal reduced total transform. The node may be a self-intersection of a component. -/
theorem atWorstNodalOfRelativeDimensionOne_radical_comap_blowupToBase_of_node
    (hnode : D.IsNodeOfReducedBoundary base (x)) :
    AtWorstNodalOfRelativeDimensionOne ((R).subschemeι ≫ (π) ≫ base) := by
  classical
  have : IsReduced D.subscheme := hnodal.isReduced
  obtain ⟨q, hq, hqnode⟩ := (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp hnode
  have heq : q = p := D.subschemeι.injective hq
  subst q
  choose W j hOpen hMem hNodal using
    fun z ↦ exists_nodal_neighbourhood_radical_comap hnodal hD hp z hqnode
  let (z : (R).subscheme) : IsOpenImmersion (j z) := hOpen z
  let cover : (R).subscheme.OpenCover :=
    Scheme.Cover.mkOfCovers (R).subscheme W j (fun z ↦ ⟨z, hMem z⟩)
  exact IsZariskiLocalAtSource.of_openCover (P := @AtWorstNodalOfRelativeDimensionOne) cover hNodal

omit [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))] in
include hnodal hp in
/-- A singular point of the reduced total boundary of a nodal blowup lies on the
strict transform. Away from the strict transform the boundary is the smooth
exceptional curve. -/
theorem mem_strictTransform_of_notMem_smoothLocus
    (hN : AtWorstNodalOfRelativeDimensionOne ((R).subschemeι ≫ (π) ≫ base))
    {z : (R).subscheme}
    (hz : letI := hN.syntomic; z ∉ ((R).subschemeι ≫ (π) ≫ base).smoothLocus) :
    (R).subschemeι z ∈ (S).support := by
  have := hN.syntomic
  by_contra hzS
  have : IsReduced D.subscheme := hnodal.isReduced
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian base
  have := isRegularLocalRing_stalk_of_smooth base (x)
  have hdim :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp inferInstance).2 _ hp
  have : IsReduced (E).subscheme :=
    @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hp)
  have hDI : D ≤ (I) :=
    ((D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr
      (D.range_subschemeι.le (Set.mem_range_self p))).trans
      (X.ker_fromSpecResidueField_eq_vanishingIdeal (x)).le
  have hR := (I).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI
  let U : (I).blowup.Opens := (S).support.compl
  have hS : (S).comap U.ι = ⊤ := (comap_eq_top_iff _ _).mpr (Scheme.Opens.ι_preimage_self _)
  have heq : (R).comap U.ι = (E).comap U.ι := by rw [hR, comap_mul, hS, top_mul]
  let J := (R).comap U.ι
  let j := subschemeMap J (R) U.ι (le_map_comap _ _)
  let i := subschemeMap J (E) U.ι (le_map_iff_comap_le.mpr heq.ge)
  have hj : IsPullback J.subschemeι j U.ι (R).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [j]) (by simp [J])
  have hi : IsPullback J.subschemeι i U.ι (E).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [i]) (by simpa [J] using heq.symm)
  have : IsOpenImmersion j := MorphismProperty.of_isPullback hj inferInstance
  have : IsOpenImmersion i := MorphismProperty.of_isPullback hi inferInstance
  have := smoothOfRelativeDimension_exceptional (k := k) hp
  have : Smooth ((E).subschemeι ≫ (π) ≫ base) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hcomp : j ≫ (R).subschemeι ≫ (π) ≫ base = i ≫ (E).subschemeι ≫ (π) ≫ base := by
    rw [← hj.w_assoc, ← hi.w_assoc]
  have : Smooth (j ≫ (R).subschemeι ≫ (π) ≫ base) := hcomp.symm ▸ inferInstance
  obtain ⟨w, rfl⟩ : z ∈ Set.range j := by
    rw [Scheme.Pullback.range_snd_of_isPullback hj]
    exact ⟨⟨(R).subschemeι z, hzS⟩, rfl⟩
  apply hz
  have hw : w ∈ (j ≫ (R).subschemeι ≫ (π) ≫ base).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rwa [← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at hw

end

variable {D : X.IdealSheafData} {p : X}

local notation "P" => vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "π" => blowupToBase P
local notation "E" => comap P π
local notation "R" => radical (D.comap π)
local notation "K(" Y ")" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)

/-- At a closed node of a nodal anticanonical Cartier divisor on a smooth surface,
the reduced total transform is again nodal and anticanonical. Its ideal is contained
in the exceptional ideal, and multiplying by the exceptional ideal gives the total transform. -/
theorem IsEffectiveCartier.isAnticanonical_reducedTotalTransform_of_node
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ base))
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
    (hp : IsClosed ({p} : Set X)) (hn : D.IsNodeOfReducedBoundary base p) :
    letI : (P).blowup.Over (Spec (.of k)) := ⟨π ≫ base⟩
    letI : SmoothOfRelativeDimension 2 ((P).blowup ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowup_closed_point base hp
    ∃ hR : (R).IsEffectiveCartier,
      LineBundleClass.mk hR.toInvertibleSheaf = K((P).blowup) ∧
      D.comap π = R * E ∧ R ≤ E ∧
      AtWorstNodalOfRelativeDimensionOne ((R).subschemeι ≫ π ≫ base) := by
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType base
  have : IsReduced D.subscheme := hN.isReduced
  have hpD := mem_support_of_isNodeOfReducedBoundary hn
  have hDI : D ≤ P :=
    (X.ker_fromSpecResidueField_eq_vanishingIdeal p) ▸
      (D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr hpD
  have horder : D.stalkOrder p = 2 := by
    simpa only [ite_eq_left hn] using hD.stalkOrder_eq_if_isNodeOfReducedBoundary hN hpD
  have h := hD.exists_anticanonical_strictTransform_mul_exceptional_pow k hp hpD hK
  dsimp only at h
  have : IsIntegral (P).blowup := isIntegral_blowup_closed_point base hp
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp
    inferInstance).2 p hp
  have := isRegularLocalRing_stalk_of_smooth base p
  have : Surjective π := surjective_blowupToBase_point hp hd
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hd hp
  simp only [horder, ENat.toNat_ofNat, Nat.reduceSub, pow_one] at h
  have hN' : AtWorstNodalOfRelativeDimensionOne ((R).subschemeι ≫ π ≫ base) := by
    obtain ⟨z, hz, -⟩ := (D.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp hn
    subst p
    exact atWorstNodalOfRelativeDimensionOne_radical_comap_blowupToBase_of_node hN hD hp hn
  have hEq := (P).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI
  have hLe : R ≤ E := hEq.trans_le (mul_le_of_le_one_left' le_top)
  obtain ⟨hOld, hc, ht⟩ := h
  refine ⟨hEq.symm ▸ hOld, ?_, ?_, hLe, hN'⟩
  · rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hOld hEq]
    exact hc
  · rw [hEq]
    exact ht.symm

end AlgebraicGeometry.Scheme.IdealSheafData
