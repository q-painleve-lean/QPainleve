/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.PointBlowup
public import TauCeti.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Branches in the strict transform at a node

On the ambient blowup of a node of a closed nodal curve, the strict transform
has one point for each of the two branches over a separably closed field.
The morphism of blowups realizes the strict transform as a closed subscheme,
so the two branch points remain distinct in the ambient blowup.
-/

public section

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
