/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.PointBlowup
public import TauCeti.AlgebraicGeometry.Blowup.Pullback

import QPainleve.AlgebraicGeometry.Blowup.Comparison
import QPainleve.AlgebraicGeometry.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Branches in the strict transform at a node

On the ambient blowup of a node of a closed nodal curve, the strict transform
has one point for each of the two branches over a separably closed field.
The morphism of blowups realizes the strict transform as a closed subscheme,
so the two branch points remain distinct in the ambient blowup. Over any field,
the canonical map from the branch scheme identifies the points over the node
with the fiber of the strict transform.
-/

public noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {D Y : Scheme.{u}} [D.Over (Spec (.of k))]

/-- The fiber of the strict transform over the blown-up node is isomorphic to the
fiber of the blowup of the curve's singular locus at that node. -/
theorem nonempty_fiberToSpecResidueFieldIso_strictTransform_of_node
    (i : D ⟶ Y) [IsClosedImmersion i]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {x : D}
    (hx : (letI := hnodal.syntomic; x ∈ (D.singularLocus k).support)) :
    letI := hnodal.syntomic
    let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
    Nonempty (Over.mk ((I.blowupMap i ≫ I.blowupToBase).fiberToSpecResidueField (i x)) ≅
      Over.mk ((D.singularLocus k).blowupToBase.fiberToSpecResidueField x ≫
        Spec.map (i.residueFieldMap x))) := by
  have := hnodal.syntomic
  let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
  let f := (I.comap i).blowupToBase
  let g := I.blowupMap i ≫ I.blowupToBase
  have H : IsPullback (𝟙 _) f g i :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [g, f, Category.id_comp,
      I.blowupMap_blowupToBase]⟩
  obtain ⟨e⟩ := H.nonempty_iso_fiberToSpecResidueField x
  have hcenter : I.comap i = vanishingIdeal ⟨closure {x}, isClosed_closure⟩ :=
    comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x
  obtain ⟨eNode⟩ := D.nonempty_fiberToSpecResidueFieldIso_blowup_singularLocus_of_node hnodal hx
  let gκ := Spec.map (i.residueFieldMap x)
  have hEq := congrArg
    (fun L : D.IdealSheafData ↦ Over.mk (L.blowupToBase.fiberToSpecResidueField x ≫ gκ)) hcenter
  exact ⟨e.symm ≪≫ eqToIso hEq ≪≫ (Over.map gκ).mapIso eNode⟩

/-- Above a node, the scheme-theoretic strict transform of a closed nodal curve has
two points over a separably closed field. This includes nodes on a single component. -/
theorem natCard_preimage_strictTransform_eq_two_of_node [IsSepClosed k]
    (i : D ⟶ Y) [IsClosedImmersion i]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {x : D}
    (hx : (letI := hnodal.syntomic; x ∈ (D.singularLocus k).support)) :
    let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
    Nat.card ((I.blowupMap i ≫ I.blowupToBase) ⁻¹' {i x}) = 2 := by
  have := hnodal.syntomic
  let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
  let f := I.blowupMap i ≫ I.blowupToBase
  let s := (D.singularLocus k).blowupToBase
  obtain ⟨e⟩ := nonempty_fiberToSpecResidueFieldIso_strictTransform_of_node i hnodal hx
  let p := (Scheme.homeoOfIso ((Over.forget _).mapIso e)).toEquiv
  let ePoints := ((f.fiberHomeo (i x)).toEquiv.symm.trans p).trans (s.fiberHomeo x).toEquiv
  exact (Nat.card_congr ePoints).trans
    (D.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support hnodal hx)

/-- The strict transform of a closed nodal curve is regular at every point above the
blown-up node. Other nodes on the original curve are allowed. -/
theorem isRegularLocalRing_stalk_strictTransform_of_node
    (i : D ⟶ Y) [IsClosedImmersion i]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {x : D}
    (hx : (letI := hnodal.syntomic; x ∈ (D.singularLocus k).support)) :
    let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
    ∀ y : (I.comap i).blowup, (I.blowupMap i ≫ I.blowupToBase) y = i x →
      IsRegularLocalRing ((I.comap i).blowup.presheaf.stalk y) := by
  let I := vanishingIdeal (⟨closure {i x}, isClosed_closure⟩ : Closeds Y)
  have hcenter : I.comap i = vanishingIdeal ⟨closure {x}, isClosed_closure⟩ :=
    comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x
  have hreg := D.isRegularLocalRing_stalk_blowupToBase_vanishingIdeal_of_node hnodal hx
  dsimp only
  rw [I.blowupMap_blowupToBase]
  intro y hy
  have hxy : (I.comap i).blowupToBase y = x :=
    i.isClosedEmbedding.injective (by simpa only [Scheme.Hom.comp_apply] using hy)
  exact (hcenter.symm ▸ hreg) y hxy

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

variable {k : Type u} [Field k] {D Y : Scheme.{u}} [D.Over (Spec (.of k))]
  (i : D ⟶ Y) [IsClosedImmersion i]
  (hnodal : AtWorstNodalOfRelativeDimensionOne (D ↘ Spec (.of k))) {x : D}
  (hx : (letI := hnodal.syntomic; x ∈ (D.singularLocus k).support))

local notation "J" =>
  comap (vanishingIdeal (Closeds.mk (closure (singleton (i x))) isClosed_closure)) i

include hx in
/-- The strict transform center pulls back to an effective Cartier divisor on the
blowup of the curve's singular locus. -/
theorem isEffectiveCartier_comap_strictTransformCenter :
    letI := hnodal.syntomic
    ((J).comap (D.singularLocus k).blowupToBase).IsEffectiveCartier := by
  have := hnodal.syntomic
  rw [comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x]
  exact D.isEffectiveCartier_comap_blowupToBase_singularLocus_of_node hnodal hx

/-- The blowup of the singular locus of the curve lifts to its strict transform
in the ambient blowup at the specified node. -/
def normalizationToStrictTransform :
    letI := hnodal.syntomic
    (D.singularLocus k).blowup ⟶ (J).blowup := by
  letI := hnodal.syntomic
  exact (J).blowupLift _ (isEffectiveCartier_comap_strictTransformCenter i hnodal hx)

/-- The normalization lift to the strict transform commutes with the projections to the curve. -/
@[reassoc]
theorem normalizationToStrictTransform_blowupToBase :
    letI := hnodal.syntomic
    normalizationToStrictTransform i hnodal hx ≫ (J).blowupToBase =
      (D.singularLocus k).blowupToBase := by
  have := hnodal.syntomic
  exact (J).blowupLift_blowupToBase _ _

/-- The branch scheme maps to the strict transform in the ambient blowup of the
specified node. The map restricts the lift of the normalization morphism. -/
@[expose]
def strictTransformBranchMap :
    letI := hnodal.syntomic
    D.branchScheme k ⟶ (J).blowup := by
  letI := hnodal.syntomic
  exact D.branchSchemeToBlowup k ≫ normalizationToStrictTransform i hnodal hx

/-- The map from the branch scheme to the strict transform commutes with both maps
to the original curve. -/
@[reassoc (attr := simp)]
theorem strictTransformBranchMap_blowupToBase :
    letI := hnodal.syntomic
    strictTransformBranchMap i hnodal hx ≫ (J).blowupToBase =
      D.branchSchemeToSingularLocus k ≫ (D.singularLocus k).subschemeι := by
  have := hnodal.syntomic
  rw [strictTransformBranchMap, Category.assoc, normalizationToStrictTransform_blowupToBase,
    Scheme.branchSchemeToSingularLocus_subschemeι]

/-- On the fiber over a node, the canonical branch map is a bijection to the fiber of
the strict transform. Over a separably closed field this identifies the two branches
even at a self-node. -/
theorem bijOn_strictTransformBranchMap :
    letI := hnodal.syntomic
    Set.BijOn (strictTransformBranchMap i hnodal hx)
      {q | (D.singularLocus k).subschemeι (D.branchSchemeToSingularLocus k q) = x}
      ((J).blowupToBase ⁻¹' {x}) := by
  have := hnodal.syntomic
  obtain ⟨U, hxU, h⟩ := D.exists_comap_singularLocus_eq_comap_vanishingIdeal_of_node hnodal hx
  have hJ : (D.singularLocus k).comap U.ι = (J).comap U.ι :=
    h.trans (congrArg (fun L : D.IdealSheafData ↦ L.comap U.ι)
      (comap_vanishingIdeal_closure_singleton_of_isClosedImmersion i x)).symm
  have hν :=
    bijOn_fiber_of_comap_eq (normalizationToStrictTransform_blowupToBase i hnodal hx) hJ hxU
  let a := D.branchSchemeToBlowup k
  let b := D.branchSchemeToSingularLocus k ≫ (D.singularLocus k).subschemeι
  let ν := (D.singularLocus k).blowupToBase
  let H := D.isPullback_branchScheme k
  have hb : (a ≫ ν) = b := (D.branchSchemeToSingularLocus_subschemeι k).symm
  have ha : Set.BijOn a (b ⁻¹' {x}) (ν ⁻¹' {x}) := by
    have : IsClosedImmersion a := MorphismProperty.of_isPullback H inferInstance
    refine ⟨?_, a.isClosedEmbedding.injective.injOn, ?_⟩
    · intro y hy
      simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, hb] using hy
    · intro y hy
      obtain ⟨z, hz⟩ : x ∈ Set.range (D.singularLocus k).subschemeι :=
        (D.singularLocus k).range_subschemeι.ge hx
      obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback H z y
        (hz.trans (Set.mem_singleton_iff.mp hy).symm)
      have hq' : a q = y := hq
      have hqBase : b q = ν y := by rw [← hb, Scheme.Hom.comp_apply, hq']
      exact ⟨q, hqBase.trans (Set.mem_singleton_iff.mp hy), hq'⟩
  exact hν.comp ha

/-- The actual branches over a node are equivalent to the points of the ambient
strict transform over that node. -/
def strictTransformBranchEquiv :
    letI := hnodal.syntomic
    ({q | (D.singularLocus k).subschemeι (D.branchSchemeToSingularLocus k q) = x} :
      Set (D.branchScheme k)) ≃ ((J).blowupToBase ⁻¹' {x} : Set (J).blowup) :=
  (bijOn_strictTransformBranchMap i hnodal hx).equiv _

/-- The forward map of the branch equivalence is induced by the canonical scheme
morphism from the branch scheme. -/
@[simp]
theorem strictTransformBranchEquiv_apply_coe :
    letI := hnodal.syntomic
    ∀ q, (strictTransformBranchEquiv i hnodal hx q).val = strictTransformBranchMap i hnodal hx q :=
  fun _ ↦ (rfl)

end AlgebraicGeometry.Scheme.Hom
