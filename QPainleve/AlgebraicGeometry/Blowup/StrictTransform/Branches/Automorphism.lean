/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Naturality
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.FixedBranches

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Nodality
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Locality
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Automorphisms at the attachments of a nodal blowup

When an automorphism fixes the branches of a node, its lift fixes the two
attachment points on the exceptional divisor. At each attachment it also fixes
the branches of the reduced total transform, one on the strict transform and
one on the exceptional divisor.

This is the local comparison for the passage through toric blowups in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}}
  {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)

local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "C" => subscheme D

variable [D.subscheme.Over (Spec (.of k))]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
  {p : D.subscheme} (hp : (letI := hnodal.syntomic; p ∈ (D.subscheme.singularLocus k).support))
  (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "I" =>
  vanishingIdeal (Closeds.mk (closure (singleton (D.subschemeι p))) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "S" => Scheme.Hom.ker (blowupMap I (D.subschemeι))
local notation "E" => Scheme.IdealSheafData.comap (I) (π)
local notation "totalBoundary" => radical (D.comap (π))

local notation "B" => subscheme (totalBoundary)
local notation "j" => subschemeι (totalBoundary)

section Surface

variable [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

include hD hc hnodal in
private theorem attachment_mem_closure_sides {z : B} (hzS : (j) z ∈ (S).support)
    (hzE : (j) z ∈ (E).support) :
    let U := (j) ⁻¹ᵁ (E).support.compl
    let V := (j) ⁻¹ᵁ (S).support.compl
    Disjoint U V ∧ z ∈ closure (U : Set B) ∧ z ∈ closure (V : Set B) := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have := isRegularLocalRing_stalk_of_smooth s (D.subschemeι p)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp
    inferInstance).2 _ hc
  let : IsIntegral (vanishingIdeal
      ⟨closure (singleton (D.subschemeι p)), isClosed_closure⟩).blowup :=
    isIntegral_blowup_closed_point s hc
  have : Surjective (π) := surjective_blowupToBase_point hc hdim
  have : IsLocallyNoetherian (I).blowup := LocallyOfFiniteType.isLocallyNoetherian (π)
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hc
  have : IsReduced D.subscheme := hnodal.isReduced
  have hDI : D ≤ (I) := (X.ker_fromSpecResidueField_eq_vanishingIdeal (D.subschemeι p)) ▸
    (D.le_ker_fromSpecResidueField_iff_mem_support hc).mpr
      (D.range_subschemeι.le (Set.mem_range_self _))
  have hcover : (totalBoundary).support = (S).support ⊔ (E).support := by
    rw [(I).radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul D hDI, support_mul]
  have hdiv := hD.exists_strictTransform_cartierDivisor hc hdim (hD.comap_of_isDominant (π))
  let q := (E).subschemeι (genericPoint (E).subscheme)
  have hq : q ∈ (E).support := (E).range_subschemeι.le (Set.mem_range_self _)
  have hq' : q ∉ (S).support :=
    hdiv.choose_spec.2 ⟨q, (I).isEffectiveCartier_comap_blowupToBase
      |>.coheight_subschemeι_genericPoint⟩ hq
  have hE : IsIrreducible ((E).support : Set (I).blowup) := by
    rw [← (E).range_subschemeι]
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (↥(E).subscheme)).image
        (E).subschemeι (E).subschemeι.continuous.continuousOn
  have hEcl := subset_closure_inter_of_isPreirreducible_of_isOpen hE.isPreirreducible
    (S).support.isClosed.isOpen_compl ⟨q, hq, hq'⟩ hzE
  have hScl : (j) z ∈ closure (((totalBoundary).support : Set (I).blowup) \ (E).support) := by
    have hS := congrArg (fun J : (I).blowup.IdealSheafData ↦
      (J.support : Set (I).blowup)) ((I).ker_blowupMap_subschemeι_eq_vanishingIdeal D)
    rw [coe_support_vanishingIdeal, Closeds.coe_closure] at hS
    rw [support_radical, ← hS]
    exact hzS
  refine ⟨Opens.coe_disjoint.mp ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxU hxV
    have hx := (totalBoundary).range_subschemeι.le (Set.mem_range_self x)
    rw [hcover, Closeds.coe_sup, Set.mem_union] at hx
    exact hx.elim hxV hxU
  simp only [Scheme.Hom.coe_preimage, Closeds.coe_compl,
    (j).isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image,
    Set.image_preimage_eq_inter_range, (totalBoundary).range_subschemeι, Set.inter_comm (_ᶜ)]
  refine ⟨hScl, ?_⟩
  apply closure_mono _ hEcl
  rw [hcover, Closeds.coe_sup]
  exact Set.inter_subset_inter_left _ Set.subset_union_right

end Surface

variable (e : X ≅ X) (d : D.subscheme ≅ D.subscheme) [d.hom.IsOver (Spec (.of k))]
  (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom) (hfix : d.hom p = p)

local notation "he" => comap_nodeIdeal_eq_of_iso D.subschemeι D.subschemeι d e hd hfix
local notation "l" => blowupIso I e he

variable (r :
    (D.comap
      (vanishingIdeal
        ⟨closure (singleton (D.subschemeι p)), isClosed_closure⟩).blowupToBase).radical.subscheme ≅
    (D.comap
      (vanishingIdeal
        ⟨closure (singleton (D.subschemeι p)), isClosed_closure⟩).blowupToBase).radical.subscheme)

include hp hc in
private theorem fixes_attachment_of_fixes_branches
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hbranches : letI := hnodal.syntomic
      ∀ q : (C).branchScheme k,
        ((C).branchSchemeToSingularLocus k ≫ ((C).singularLocus k).subschemeι) q = p →
          (d.branchSchemeIso (R := k)).hom q = q)
    {z : B} (hzS : (j) z ∈ (S).support) (hzE : (j) z ∈ (E).support) :
    r.hom z = z := by
  have := hnodal.syntomic
  let f := (I).blowupMap D.subschemeι
  have hS : ((S).support : Set (I).blowup) = Set.range f := by
    rw [support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]
  have hyS : (j) z ∈ Set.range f := by rw [← hS]; exact hzS
  obtain ⟨y, hy⟩ := hyS
  have hyp : ((I).comap D.subschemeι).blowupToBase y = p := by
    apply D.subschemeι.injective
    have hjp : (π) ((j) z) = D.subschemeι p := by
      have h := hzE
      rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage,
        coe_support_vanishingIdeal] at h
      have hclose := congrArg (fun Q : Set X ↦ (π) ((j) z) ∈ Q) hc.closure_eq
      exact Set.mem_singleton_iff.mp (hclose.mp h)
    have hw := congrArg (fun a : ((I).comap D.subschemeι).blowup ⟶ X ↦ a y)
      (blowupMap_blowupToBase (I) D.subschemeι)
    simp only [Scheme.Hom.comp_apply] at hw
    exact hw.symm.trans ((congrArg (π) hy).trans hjp)
  have hfixed := (blowupIso_fixes_strictTransform_fiber_iff D.subschemeι
    hnodal hp d e hd hfix).mpr hbranches y hyp
  apply (j).injective
  have hw := congrArg (fun a : B ⟶ (I).blowup ↦ a z) hr
  simp only [Scheme.Hom.comp_apply] at hw
  rw [hw, ← hy]
  exact hfixed

variable [X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [(D.comap (vanishingIdeal
    ⟨closure (singleton (D.subschemeι p)), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
      (Spec (.of k))] [r.hom.IsOver (Spec (.of k))]

include hD hp hc in
/-- The lift of a boundary automorphism fixing the branches over the blowup center
fixes both branches of the reduced total boundary at each attachment. The attachment
is a node, including when the center was a self-node of the original boundary. -/
theorem singularLocusBlowupIso_fixes_over_attachment [IsSepClosed k] [PerfectField k]
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hCOver : C ↘ Spec (.of k) = D.subschemeι ≫ s)
    (hBOver : B ↘ Spec (.of k) = j ≫ (π) ≫ s)
    (hbranches : letI := hnodal.syntomic
      ∀ q : (C).branchScheme k,
        ((C).branchSchemeToSingularLocus k ≫ ((C).singularLocus k).subschemeι) q = p →
          (d.branchSchemeIso (R := k)).hom q = q)
    {z : B} (hzS : (j) z ∈ (S).support) (hzE : (j) z ∈ (E).support) :
    ∃ hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)),
      letI := hN.syntomic
      z ∈ ((B).singularLocus k).support ∧
        ∀ {y : ((B).singularLocus k).blowup}, ((B).singularLocus k).blowupToBase y = z →
          (r.singularLocusBlowupIso (R := k)).hom y = y := by
  have := hnodal.syntomic
  have : IsReduced D.subscheme := hnodal.isReduced
  have hpNode : D.IsNodeOfReducedBoundary s (D.subschemeι p) := by
    refine (D.isNodeOfReducedBoundary_iff_of_isReduced s _).mpr ⟨p, rfl, ?_⟩
    rw [← hCOver]
    exact ((C ↘ Spec (.of k)).isNodeAt_iff_notMem_smoothLocus hnodal p).mpr
      (((C).mem_support_singularLocus_iff_notMem_smoothLocus p).mp hp)
  have hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)) := by
    rw [hBOver]
    exact atWorstNodalOfRelativeDimensionOne_radical_comap_blowupToBase_of_node
      (hCOver ▸ hnodal) hD hc hpNode
  refine ⟨hN, ?_⟩
  have hDcomap : D.comap e.hom = D := by
    calc
      _ = (d.hom ≫ D.subschemeι).ker.comap e.hom := by
        rw [Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]
      _ = D := by rw [hd, comap_ker_comp_of_isClosedImmersion, ker_subschemeι]
  have hEcomap : (E).comap (l).hom = E := comap_blowupIso_hom _ _ he
  have hScomap : (S).comap (l).hom = S := by
    rw [comap_ker_blowupMap_subschemeι_blowupIso, hDcomap]
  let U := (j) ⁻¹ᵁ (E).support.compl
  let V := (j) ⁻¹ᵁ (S).support.compl
  have hmap {J : (I).blowup.IdealSheafData} (hJ : J.comap (l).hom = J) :
      Set.MapsTo r.hom ((j) ⁻¹ᵁ J.support.compl) ((j) ⁻¹ᵁ J.support.compl) := by
    intro x hx
    have hw : (j) (r.hom x) = (l).hom ((j) x) := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : B ⟶ (I).blowup ↦ f x) hr
    have hpre := congrArg (fun K : (I).blowup.IdealSheafData ↦ (K.support : Set (I).blowup)) hJ
    rw [support_comap, Closeds.coe_preimage] at hpre
    simp only [Scheme.Hom.coe_preimage, Closeds.coe_compl, Set.mem_preimage,
      Set.mem_compl_iff] at hx ⊢
    rw [hw]
    exact fun h ↦ hx (hpre ▸ (h : (j) x ∈ (l).hom ⁻¹' (J.support : Set (I).blowup)))
  obtain ⟨hdisj, hU, hV⟩ := attachment_mem_closure_sides hD hnodal hc hzS hzE
  exact r.singularLocusBlowupIso_fixes_over_of_mem_closure hN U V hdisj
    (hmap hEcomap) (hmap hScomap) hU hV
    (fixes_attachment_of_fixes_branches hnodal hp hc e d hd hfix r hr hbranches hzS hzE)

omit [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
include hc in
private theorem fixes_over_compl_exceptional_iff
    (hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)))
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hCOver : C ↘ Spec (.of k) = D.subschemeι ≫ s)
    (hBOver : B ↘ Spec (.of k) = j ≫ (π) ≫ s) :
    letI := hnodal.syntomic
    letI := hN.syntomic
    (∀ y : ((B).singularLocus k).blowup,
      ((B).singularLocus k).blowupToBase y ∈ ((B).singularLocus k).support →
      (j) (((B).singularLocus k).blowupToBase y) ∉ (E).support →
      (r.singularLocusBlowupIso (R := k)).hom y = y) ↔
    (∀ y : ((C).singularLocus k).blowup,
      ((C).singularLocus k).blowupToBase y ∈ ((C).singularLocus k).support →
      ((C).singularLocus k).blowupToBase y ≠ p →
      (d.singularLocusBlowupIso (R := k)).hom y = y) := by
  have := hnodal.syntomic
  have := hN.syntomic
  have : IsReduced D.subscheme := hnodal.isReduced
  let f := subschemeMap (totalBoundary) D (π) (le_map_iff_comap_le.mpr (le_radical _))
  have hf : f ≫ D.subschemeι = (j) ≫ (π) := subschemeMap_subschemeι _ _ _ _
  have : f.IsOver (Spec (.of k)) := ⟨by rw [hCOver, ← Category.assoc, hf, Category.assoc, hBOver]⟩
  have hcomm : r.hom ≫ f = f ≫ d.hom := by
    rw [← cancel_mono D.subschemeι, Category.assoc, hf, Category.assoc, hd,
      ← Category.assoc f, hf, ← Category.assoc r.hom, hr, Category.assoc,
      blowupIso_hom_blowupToBase, Category.assoc]
  let U := D.subschemeι ⁻¹ᵁ (I).support.compl
  have hIso : (I).support.compl ≤ (π).isoLocus :=
    (π).le_isoLocus_iff.mpr ((I).isIso_blowupToBase_restrict_of_disjoint_support
      (by exact disjoint_compl_left))
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp
    ((D.subschemeι.preimage_mono hIso).trans (D.preimage_isoLocus_le_subschemeMap_radical (π)))
  have hmem (x : C) : x ∈ U ↔ x ≠ p := by
    dsimp only [U]
    rw [Scheme.Hom.mem_preimage, ← SetLike.mem_coe, Closeds.coe_compl,
      coe_support_vanishingIdeal]
    simp only [Closeds.coe_mk, hc.closure_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
      D.subschemeι.injective.eq_iff]
  have hU : Set.MapsTo d.hom U U := by
    intro x hx
    exact (hmem _).mpr fun eq ↦ (hmem _).mp hx (d.hom.injective (eq.trans hfix.symm))
  have hfmem (x : B) : f x ∈ U ↔ (j) x ∉ (E).support := by
    dsimp only [U]
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply]
    simp only [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Closeds.coe_compl,
      Set.mem_preimage, Set.mem_compl_iff]
  simpa only [hfmem, hmem] using
    d.singularLocusBlowupIso_fixes_over_isIso_restrict_iff r f U hU hcomm

include hD hp hc in
/-- An automorphism fixing the normalization points over every node still fixes them
after blowing up a closed node. This includes the branches over new attachment points
and the branches over nodes away from the center. -/
theorem singularLocusBlowupIso_fixes_over_nodeBlowup [IsSepClosed k] [PerfectField k]
    (hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)))
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hCOver : C ↘ Spec (.of k) = D.subschemeι ≫ s)
    (hBOver : B ↘ Spec (.of k) = j ≫ (π) ≫ s)
    (hbranches : letI := hnodal.syntomic
      ∀ y : ((C).singularLocus k).blowup,
        ((C).singularLocus k).blowupToBase y ∈ ((C).singularLocus k).support →
          (d.singularLocusBlowupIso (R := k)).hom y = y) :
    letI := hN.syntomic
      ∀ y : ((B).singularLocus k).blowup,
        ((B).singularLocus k).blowupToBase y ∈ ((B).singularLocus k).support →
          (r.singularLocusBlowupIso (R := k)).hom y = y := by
  have := hnodal.syntomic
  have := hN.syntomic
  intro y hy
  let z := ((B).singularLocus k).blowupToBase y
  by_cases hzE : (j) z ∈ (E).support
  · have hz : z ∉ (B ↘ Spec (.of k)).smoothLocus :=
      ((B).mem_support_singularLocus_iff_notMem_smoothLocus z).mp hy
    have hN' : AtWorstNodalOfRelativeDimensionOne ((j) ≫ (π) ≫ s) := hBOver ▸ hN
    have := hN'.syntomic
    have hz' : z ∉ ((j) ≫ (π) ≫ s).smoothLocus := by
      simpa only [← hBOver] using hz
    have hS := mem_strictTransform_of_notMem_smoothLocus (hCOver ▸ hnodal) hc
      (hBOver ▸ hN) hz'
    have hF : ∀ q : (C).branchScheme k,
        ((C).branchSchemeToSingularLocus k ≫ ((C).singularLocus k).subschemeι) q = p →
        (d.branchSchemeIso (R := k)).hom q = q := by
      intro q hq
      have hpb := (C).isPullback_branchScheme k
      have : IsClosedImmersion ((C).branchSchemeToBlowup k) :=
        MorphismProperty.of_isPullback hpb inferInstance
      apply ((C).branchSchemeToBlowup k).injective
      rw [← Scheme.Hom.comp_apply, Iso.branchSchemeIso_hom_branchSchemeToBlowup,
        Scheme.Hom.comp_apply]
      apply hbranches
      rw [← Scheme.Hom.comp_apply, ← hpb.w, Scheme.Hom.comp_apply]
      rw [← Scheme.Hom.comp_apply, hq]
      exact hp
    obtain ⟨hN', h⟩ := singularLocusBlowupIso_fixes_over_attachment hD hnodal hp hc e d hd
      hfix r hr hCOver hBOver hF hS hzE
    exact h.2 rfl
  · exact (fixes_over_compl_exceptional_iff hnodal hc e d hd hfix r hN hr hCOver hBOver).mpr
      (fun x hx _ ↦ hbranches x hx) y hy hzE

include hD hp hc in
/-- Fixing the branches of the reduced total boundary fixes the original branches
over the center. Their attachment points are nodes of the new boundary. -/
private theorem fixes_branches_over_center
    (hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)))
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hbranches : letI := hN.syntomic
      ∀ y : ((B).singularLocus k).blowup,
        ((B).singularLocus k).blowupToBase y ∈ ((B).singularLocus k).support →
          (r.singularLocusBlowupIso (R := k)).hom y = y) :
    letI := hnodal.syntomic
    ∀ q : (C).branchScheme k,
      ((C).branchSchemeToSingularLocus k ≫ ((C).singularLocus k).subschemeι) q = p →
      (d.branchSchemeIso (R := k)).hom q = q := by
  have := hnodal.syntomic
  have := hN.syntomic
  have : IsReduced C := hnodal.isReduced
  let f := (I).blowupMap D.subschemeι
  refine (blowupIso_fixes_strictTransform_fiber_iff D.subschemeι hnodal hp d e hd hfix).mp ?_
  intro y hy
  have hS : f y ∈ (S).support := by
    rw [← SetLike.mem_coe, support_ker]
    exact subset_closure (Set.mem_range_self _)
  have hπ : (π) (f y) = D.subschemeι p := by
    have h := congrArg (fun a ↦ (a : _ ⟶ X) y) (blowupMap_blowupToBase (I) D.subschemeι)
    simpa only [Scheme.Hom.comp_apply, hy] using h
  have hE : f y ∈ (E).support := by
    rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage,
      hπ, coe_support_vanishingIdeal]
    exact subset_closure (Set.mem_singleton _)
  have hfB : f y ∈ (totalBoundary).support := by
    rw [support_radical, support_comap, ← SetLike.mem_coe, Closeds.coe_preimage,
      Set.mem_preimage, hπ]
    exact D.range_subschemeι.le (Set.mem_range_self _)
  obtain ⟨z, hz⟩ := (totalBoundary).range_subschemeι.ge hfB
  obtain ⟨hUV, hU, hV⟩ := attachment_mem_closure_sides hD hnodal hc (hz.symm ▸ hS) (hz.symm ▸ hE)
  have hzSing := (B).mem_support_singularLocus_of_mem_closures hN _ _ hUV hU hV
  have : Surjective ((B).singularLocus k).blowupToBase :=
    (B).surjective_blowupToBase_singularLocus hN
  obtain ⟨w, rfl⟩ := ((B).singularLocus k).blowupToBase.surjective z
  have hfixed := congrArg (fun a : ((B).singularLocus k).blowup ⟶ B ↦ a w)
    (r.singularLocusBlowupIso_hom_blowupToBase (R := k))
  simp only [Scheme.Hom.comp_apply, hbranches w hzSing] at hfixed
  have h := congrArg (fun a : B ⟶ (I).blowup ↦ a ((B).singularLocus k |>.blowupToBase w)) hr
  simpa only [Scheme.Hom.comp_apply, ← hfixed, hz] using h.symm

include hD hp hc in
/-- Branch fixation descends through the blowup of a closed node. The two
attachments above the center distinguish the original branches even at a self-node. -/
theorem singularLocusBlowupIso_fixes_over_of_nodeBlowup
    (hN : AtWorstNodalOfRelativeDimensionOne (B ↘ Spec (.of k)))
    (hr : r.hom ≫ j = j ≫ (l).hom)
    (hCOver : C ↘ Spec (.of k) = D.subschemeι ≫ s)
    (hBOver : B ↘ Spec (.of k) = j ≫ (π) ≫ s)
    (hbranches : letI := hN.syntomic
      ∀ y : ((B).singularLocus k).blowup,
        ((B).singularLocus k).blowupToBase y ∈ ((B).singularLocus k).support →
          (r.singularLocusBlowupIso (R := k)).hom y = y) :
    letI := hnodal.syntomic
    ∀ y : ((C).singularLocus k).blowup,
      ((C).singularLocus k).blowupToBase y ∈ ((C).singularLocus k).support →
        (d.singularLocusBlowupIso (R := k)).hom y = y := by
  have := hnodal.syntomic
  have := hN.syntomic
  intro y hy
  by_cases hyP : ((C).singularLocus k).blowupToBase y = p
  · have hpb := (C).isPullback_branchScheme k
    obtain ⟨q, rfl⟩ : y ∈ Set.range ((C).branchSchemeToBlowup k) := by
      rw [Scheme.Pullback.range_snd_of_isPullback hpb, IdealSheafData.range_subschemeι]
      exact hy
    have hq : ((C).branchSchemeToSingularLocus k ≫ ((C).singularLocus k).subschemeι) q = p := by
      rw [hpb.w, Scheme.Hom.comp_apply]
      exact hyP
    have hfixq := fixes_branches_over_center hD hnodal hp hc e d hd hfix r hN hr hbranches q hq
    have h := congrArg (fun a : (C).branchScheme k ⟶ ((C).singularLocus k).blowup ↦ a q)
      (d.branchSchemeIso_hom_branchSchemeToBlowup (R := k))
    simpa only [Scheme.Hom.comp_apply, hfixq] using h.symm
  · exact (fixes_over_compl_exceptional_iff hnodal hc e d hd hfix r hN hr hCOver hBOver).mp
      (fun z hz _ ↦ hbranches z hz) y hy hyP

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
