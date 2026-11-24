/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Basic

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Nodality
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Etale
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.FixedBranches
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Attachment nodes of a reduced total boundary

Blowing up a closed node replaces it with one attachment node for each of its
branches. The identification uses the morphism from the branch scheme to the
strict transform, so it distinguishes the two branches of a self-node.
Off the center, the boundary projection bijects the nodes. These are the node
correspondences of a simple toric blowup in [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}} {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier) [D.subscheme.Over (Spec (.of k))]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
  {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "I" =>
  vanishingIdeal (Closeds.mk (closure (singleton (D.subschemeι p))) isClosed_closure)
local notation "s" => (X ↘ Spec (CommRingCat.of k))
local notation "π" => blowupToBase (I)
local notation "S" => Scheme.Hom.ker (blowupMap I (D.subschemeι))
local notation "E" => Scheme.IdealSheafData.comap (I) (π)
local notation "totalBoundary" => radical (D.comap (π))
local notation "B" => subscheme (totalBoundary)
local notation "j" => subschemeι (totalBoundary)
local notation "f" => subschemeMap (totalBoundary) D (π)
  (le_map_iff_comap_le.mpr (le_radical _))

include hc in
/-- A point of the reduced total boundary lies on the exceptional divisor exactly when its
image on the original boundary is the blowup center. -/
theorem mem_exceptional_iff_boundaryMap_eq (z : B) :
    (j) z ∈ (E).support ↔ (f) z = p := by
  have hE : Set.range (E).subschemeι = (π) ⁻¹' {D.subschemeι p} :=
    range_subschemeι_comap_pointBlowup hc
  have h := congrArg (fun g : B ⟶ X ↦ g z)
    (subschemeMap_subschemeι (totalBoundary) D (π)
      (le_map_iff_comap_le.mpr (le_radical _)))
  simp only [Scheme.Hom.comp_apply] at h
  rw [← SetLike.mem_coe, ← (E).range_subschemeι, hE, Set.mem_preimage, Set.mem_singleton_iff,
    ← h, D.subschemeι.injective.eq_iff]

variable [hX : X.Over (Spec (.of k))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

omit [D.subscheme.Over (Spec (.of k))] in
include hX hD hc in
/-- At an attachment, the reduced boundary is approached from the strict
transform and from the exceptional divisor through disjoint opens. -/
theorem attachment_mem_closure_sides [IsReduced D.subscheme] {z : B} (hzS : (j) z ∈ (S).support)
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

variable [PerfectField k] (hCOver : D.subscheme ↘ Spec (.of k) =
    D.subschemeι ≫ (X ↘ Spec (.of k)))
variable [(D.comap (vanishingIdeal
  ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
    (Spec (.of k))]
variable (hBOver :
  (D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k) =
    (D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subschemeι ≫
        (vanishingIdeal ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase ≫
          X ↘ Spec (.of k))
variable (hp : (letI := hnodal.syntomic; p ∈ (D.subscheme.singularLocus k).support))
  (hN : AtWorstNodalOfRelativeDimensionOne
    ((D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
        Spec (.of k)))

include hD hnodal hc hBOver hCOver in
/-- A point of the reduced boundary over the center is singular exactly when
it lies on the strict transform. -/
theorem mem_support_singularLocus_iff_mem_strictTransform_of_boundaryMap_eq
    {z : B} (hz : (f) z = p) :
    letI := hN.syntomic
    z ∈ ((B).singularLocus k).support ↔ (j) z ∈ (S).support := by
  have := hN.syntomic
  refine ⟨fun hz' ↦ ?_, fun hz' ↦ ?_⟩
  · have hN' : AtWorstNodalOfRelativeDimensionOne (j ≫ (π) ≫ (s)) := hBOver ▸ hN
    have hz' := ((B).mem_support_singularLocus_iff_notMem_smoothLocus z).mp hz'
    exact mem_strictTransform_of_notMem_smoothLocus (hCOver ▸ hnodal) hc hN'
      (by simpa only [← hBOver] using hz')
  · have : IsReduced D.subscheme := hnodal.isReduced
    have hzE := (mem_exceptional_iff_boundaryMap_eq hc z).mpr hz
    obtain ⟨hUV, hU, hV⟩ := attachment_mem_closure_sides (k := k) hD hc hz' hzE
    exact (B).mem_support_singularLocus_of_mem_closures hN _ _ hUV hU hV

include hD hnodal hc hBOver hCOver in
/-- The inclusion of the reduced boundary identifies the singular points over
the center with the intersection of the strict and exceptional transforms. -/
theorem bijOn_subschemeι_singularFiber :
    letI := hN.syntomic
    Set.BijOn (j)
      {z : B | z ∈ ((B).singularLocus k).support ∧ (f) z = p}
      (((S).support : Set (I).blowup) ∩ (E).support) := by
  have := hN.syntomic
  have hs (z : B) : (f) z = p →
      (z ∈ ((B).singularLocus k).support ↔ (j) z ∈ (S).support) :=
    mem_support_singularLocus_iff_mem_strictTransform_of_boundaryMap_eq
      hD hnodal hc hCOver hBOver hN
  refine ⟨fun z hz ↦ ⟨(hs z hz.2).mp hz.1,
    (mem_exceptional_iff_boundaryMap_eq hc z).mpr hz.2⟩, (j).injective.injOn, ?_⟩
  intro y hy
  have hER : (E).support ≤ (totalBoundary).support := by
    rw [support_radical, support_comap, support_comap]
    have hsupport : ((I).support : Set X) = {D.subschemeι p} :=
      (coe_support_vanishingIdeal _).trans hc.closure_eq
    simp only [← SetLike.coe_subset_coe, Closeds.coe_preimage]
    exact Set.preimage_mono (hsupport.symm ▸
      Set.singleton_subset_iff.mpr (D.range_subschemeι.le (Set.mem_range_self p)))
  obtain ⟨z, rfl⟩ := (totalBoundary).range_subschemeι.ge (hER hy.2)
  have hz := (mem_exceptional_iff_boundaryMap_eq hc z).mp hy.2
  exact ⟨z, ⟨(hs z hz).mpr hy.1, hz⟩, rfl⟩

omit [IsIntegral X] in
include hc in
private theorem bijOn_blowupMap_strictTransformFiber :
    Set.BijOn ((I).blowupMap D.subschemeι) (((I).comap D.subschemeι).blowupToBase ⁻¹' {p})
      (((S).support : Set (I).blowup) ∩ (E).support) := by
  let g := (I).blowupMap D.subschemeι
  have hg : ∀ y, g y ∈ (E).support ↔ ((I).comap D.subschemeι).blowupToBase y ∈ ({p} : Set _) := by
    intro y
    rw [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage,
      coe_support_vanishingIdeal, Closeds.coe_mk]
    have h := congrArg (fun t : ((I).comap D.subschemeι).blowup ⟶ X ↦ t y)
      (blowupMap_blowupToBase (I) D.subschemeι)
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    simp only [hc.closure_eq, Set.mem_singleton_iff, D.subschemeι.injective.eq_iff]
  have hS : ((S).support : Set (I).blowup) = Set.range g := by
    rw [support_ker, g.isClosedEmbedding.isClosed_range.closure_eq]
  refine ⟨fun y hy ↦ ⟨hS.ge (Set.mem_range_self y), (hg y).mpr hy⟩,
    g.injective.injOn, ?_⟩
  intro z hz
  obtain ⟨y, rfl⟩ := hS.le hz.1
  exact ⟨y, (hg y).mp hz.2, rfl⟩

include hD hnodal hc hCOver hBOver hp in
/-- The branches of the blown-up node biject to the nodes of the reduced total
boundary lying over it. Each branch goes to its strict-transform attachment. -/
def branchEquivSingularFiber :
    letI := hnodal.syntomic
    letI := hN.syntomic
    {q : D.subscheme.branchScheme k |
      (D.subscheme.singularLocus k).subschemeι (D.subscheme.branchSchemeToSingularLocus k q) = p}
      ≃ {z : B | z ∈ ((B).singularLocus k).support ∧ (f) z = p} := by
  have := hnodal.syntomic
  have := hN.syntomic
  exact (((bijOn_blowupMap_strictTransformFiber hc).comp
    (bijOn_strictTransformBranchMap D.subschemeι hnodal hp)).equiv _).trans
      ((bijOn_subschemeι_singularFiber hD hnodal hc hCOver hBOver hN).equiv _).symm

include hD hnodal hc hCOver hBOver hp in
/-- In the ambient blowup the new node is the image of the original branch
under the map from the branch scheme through the strict transform. -/
@[simp]
theorem subschemeι_branchEquivSingularFiber :
    letI := hnodal.syntomic
    letI := hN.syntomic
    ∀ q, (j) (branchEquivSingularFiber hD hnodal hc hCOver hBOver hp hN q).val =
      (I).blowupMap D.subschemeι (strictTransformBranchMap D.subschemeι hnodal hp q.val) := by
  have := hnodal.syntomic
  have := hN.syntomic
  intro q
  exact congrArg Subtype.val (((bijOn_subschemeι_singularFiber
    hD hnodal hc hCOver hBOver hN).equiv _).apply_symm_apply _)

omit [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [PerfectField k] in
include hc hCOver hBOver in
variable (D) in
/-- Away from the center, the map from the reduced total boundary identifies
its nodes with the original nodes other than the one blown up. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.bijOn_support_singularLocus_off_blowup :
    letI := hnodal.syntomic
    letI := hN.syntomic
    Set.BijOn (f) {z : B | (f) z ≠ p ∧ z ∈ ((B).singularLocus k).support}
      {q : D.subscheme | q ≠ p ∧ q ∈ (D.subscheme.singularLocus k).support} := by
  have := hnodal.syntomic
  have := hN.syntomic
  have : IsReduced D.subscheme := hnodal.isReduced
  let U := D.subschemeι ⁻¹ᵁ (I).support.compl
  have hIso : (I).support.compl ≤ (π).isoLocus :=
    (π).le_isoLocus_iff.mpr
      ((I).isIso_blowupToBase_restrict_of_disjoint_support disjoint_compl_left)
  have : IsIso ((f) ∣_ U) := (f).le_isoLocus_iff.mp
    ((D.subschemeι.preimage_mono hIso).trans (D.preimage_isoLocus_le_subschemeMap_radical (π)))
  have : (f).IsOver (Spec (.of k)) := ⟨by
    rw [hCOver, ← Category.assoc, subschemeMap_subschemeι, Category.assoc, hBOver]⟩
  have hmem (x : D.subscheme) : x ∈ U ↔ x ≠ p := by
    dsimp only [U]
    rw [Scheme.Hom.mem_preimage, ← SetLike.mem_coe, Closeds.coe_compl,
      coe_support_vanishingIdeal]
    simp only [Closeds.coe_mk, hc.closure_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
      D.subschemeι.injective.eq_iff]
  simpa only [Set.inter_def, SetLike.mem_coe, Scheme.Hom.mem_preimage, hmem] using
    (f).bijOn_support_singularLocus_of_isIso_morphismRestrict (R := k) U

omit [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [PerfectField k] in
include hc hCOver hBOver hp in
variable (D) in
/-- The reduced boundary projection of a nodal blowup sends nodes to nodes. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mapsTo_support_singularLocus_nodalBlowup :
    letI := hnodal.syntomic
    letI := hN.syntomic
    Set.MapsTo (f) ((B).singularLocus k).support (D.subscheme.singularLocus k).support := by
  have := hnodal.syntomic
  have := hN.syntomic
  intro q hq
  by_cases hh : (f) q = p
  · exact hh.symm ▸ hp
  · exact ((D.bijOn_support_singularLocus_off_blowup hnodal hc hCOver hBOver hN).mapsTo
      ⟨hh, hq⟩).2

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
