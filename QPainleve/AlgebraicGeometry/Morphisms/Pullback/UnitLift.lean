/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Lifting units across pullbacks of closed immersions

A unit on the overlap of a finite map and a closed immersion lifts to the
inverse image of a suitable affine neighborhood of each base point.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

namespace CategoryTheory.IsPullback

universe u

variable {P Y Z X : Scheme.{u}} {j : P ⟶ Y} {g : P ⟶ Z} {f : Y ⟶ X} {i : Z ⟶ X}

/-- For a closed immersion obtained by base change along a finite map, a unit on the
closed subscheme lifts on the inverse image of a suitable affine neighborhood of
each base point. -/
theorem exists_affineOpen_unit_lift [IsFinite f] [IsClosedImmersion i]
    (h : IsPullback j g f i) (a : Γ(P, ⊤)ˣ) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.val) (b : Γ(Y, f ⁻¹ᵁ U.val)ˣ),
      j.app (f ⁻¹ᵁ U.val) (b : Γ(Y, f ⁻¹ᵁ U.val)) =
        P.presheaf.map (j ⁻¹ᵁ (f ⁻¹ᵁ U.val)).leTop.op (a : Γ(P, ⊤)) := by
  by_cases hx : x ∈ Set.range i
  · -- Lift the function on an affine neighborhood, then exclude the image of its nonunit locus.
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have : IsClosedImmersion j := MorphismProperty.of_isPullback h.flip inferInstance
    obtain ⟨b, hb⟩ := j.app_surjective (f ⁻¹ᵁ U) (hU.preimage f)
      (P.presheaf.map (j ⁻¹ᵁ (f ⁻¹ᵁ U)).leTop.op (a : Γ(P, ⊤)))
    let V : X.Opens := ⟨(f '' (Y.basicOpen b : Set Y)ᶜ)ᶜ,
      (f.isClosedMap _ (Y.basicOpen b).isOpen.isClosed_compl).isOpen_compl⟩
    have hr := Scheme.Pullback.range_fst_of_isPullback h
    have hV : x ∈ V := by
      rintro ⟨y, hy, rfl⟩
      have hyi : y ∈ f ⁻¹' Set.range i := hx
      rw [← hr] at hyi
      obtain ⟨p, rfl⟩ := hyi
      apply hy
      have hp : p ∈ P.basicOpen (j.app (f ⁻¹ᵁ U) b) := by
        rw [hb, P.basicOpen_of_isUnit (a.isUnit.map (P.presheaf.map _).hom)]
        exact hxU
      rwa [← j.preimage_basicOpen] at hp
    obtain ⟨W, hW, hxW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (Opens.mem_inf.mpr ⟨hxU, hV⟩)
    have hw : f ⁻¹ᵁ W ≤ Y.basicOpen b :=
      fun y hy ↦ by
        by_contra hn
        exact (hWV hy).2 ⟨y, hn, rfl⟩
    let b' := Y.presheaf.map (homOfLE (hw.trans (Y.basicOpen_le b))).op b
    have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op b) :=
      Y.toRingedSpace.isUnit_res_basicOpen b
    have heq : (homOfLE (Y.basicOpen_le b)).op ≫ (homOfLE hw).op =
        (homOfLE (hw.trans (Y.basicOpen_le b))).op := Subsingleton.elim _ _
    have hb' : IsUnit b' := by
      simpa only [b', ← CommRingCat.comp_apply, ← Functor.map_comp, heq] using
        hu.map (Y.presheaf.map (homOfLE hw).op).hom
    refine ⟨⟨W, hW⟩, hxW, hb'.unit, ?_⟩
    -- Read the section map on the underlying open of the affine neighborhood.
    change j.app (f ⁻¹ᵁ W) (↑hb'.unit) =
      P.presheaf.map (j ⁻¹ᵁ (f ⁻¹ᵁ W)).leTop.op (a : Γ(P, ⊤))
    rw [IsUnit.unit_spec]
    dsimp only [b']
    have he := ConcreteCategory.congr_hom
      (j.naturality (homOfLE (hw.trans (Y.basicOpen_le b))).op) b
    simp only [CommRingCat.comp_apply, hb, ← Functor.map_comp_apply] at he
    refine he.trans ?_
    congr 2
  · -- Away from the closed subscheme the overlap is empty, so the unit 1 suffices.
    let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V) hx
    have hempty : j ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊥ := by
      apply eq_bot_iff.mpr
      intro p hp
      have he : f (j p) = i (g p) := congrArg (fun m : P ⟶ X ↦ m p) h.w
      have hpi : i (g p) ∈ U := he ▸ hp
      exact (hUV hpi) ⟨g p, rfl⟩
    have : Subsingleton Γ(P, j ⁻¹ᵁ (f ⁻¹ᵁ U)) := hempty ▸ inferInstance
    exact ⟨⟨U, hU⟩, hxU, 1, Subsingleton.elim _ _⟩

end CategoryTheory.IsPullback
