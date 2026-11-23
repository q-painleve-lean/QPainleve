/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Composition and local properties of isomorphism loci

For a surjective first map and a separated, universally closed second map with reduced
intermediate scheme, the centre of their composite is the union of the second centre and
the image of the first. Over the isomorphism locus, a morphism is injective, induces
isomorphisms on stalks, and preserves codimension.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- For a surjective first map and a separated, universally closed second map, the centre of
the composite is the union of the second centre and the image of the first, provided the
intermediate scheme is reduced. -/
theorem centre_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [IsReduced Y]
    [IsSeparated g] [UniversallyClosed g] :
    (f ≫ g).centre = g.centre ∪ g '' f.centre := by
  apply compl_injective
  ext z
  simp only [Set.mem_compl_iff, Set.mem_union, not_or]
  rw [centre_def (f ≫ g), centre_def g]
  simp only [Set.mem_compl_iff, not_not, SetLike.mem_coe]
  constructor
  · intro hz
    let U := (f ≫ g).isoLocus
    have hU : IsIso ((f ≫ g) ∣_ U) := (f ≫ g).le_isoLocus_iff.mp le_rfl
    have hcomp : IsIso (f ∣_ (g ⁻¹ᵁ U) ≫ g ∣_ U) := morphismRestrict_comp f g U ▸ hU
    have : IsClosedImmersion (f ∣_ (g ⁻¹ᵁ U) ≫ g ∣_ U) := inferInstance
    have : IsClosedImmersion (f ∣_ (g ⁻¹ᵁ U)) := .of_comp _ (g ∣_ U)
    have : Surjective (f ∣_ (g ⁻¹ᵁ U)) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip ‹Surjective f›
    have hfIso : IsIso (f ∣_ (g ⁻¹ᵁ U)) := isIso_of_isClosedImmersion_of_surjective _
    have hgIso : IsIso (g ∣_ U) := IsIso.of_isIso_comp_left (f ∣_ (g ⁻¹ᵁ U)) _
    refine ⟨g.le_isoLocus_iff.mpr hgIso hz, ?_⟩
    rintro ⟨y, hy, rfl⟩
    have hnot : y ∉ (f.isoLocus : Set Y) := by simpa only [centre_def, Set.mem_compl_iff] using hy
    exact hnot (f.le_isoLocus_iff.mpr hfIso (g.mem_preimage.mpr hz))
  · rintro ⟨hz, hImage⟩
    let W : Z.Opens := ⟨(g '' f.centre)ᶜ, (g.isClosedMap _ f.isClosed_centre).isOpen_compl⟩
    let U := g.isoLocus ⊓ W
    have hU : z ∈ U := ⟨hz, hImage⟩
    have hV : g ⁻¹ᵁ U ≤ f.isoLocus := by
      intro y hy
      by_contra hnot
      have hy' : y ∉ (f.isoLocus : Set Y) := hnot
      have hyc : y ∈ f.centre := by simpa only [centre_def, Set.mem_compl_iff] using hy'
      exact (g.mem_preimage.mp hy).2 ⟨y, hyc, rfl⟩
    have hgIso : IsIso (g ∣_ U) := g.le_isoLocus_iff.mp inf_le_left
    have hfIso : IsIso (f ∣_ (g ⁻¹ᵁ U)) := f.le_isoLocus_iff.mp hV
    refine (f ≫ g).mem_isoLocus_iff.mpr ⟨U, hU, ?_⟩
    exact (morphismRestrict_comp f g U).symm ▸ IsIso.comp_isIso' hfIso hgIso

/-- The point map is injective on the preimage of the isomorphism locus. -/
theorem injOn_preimage_isoLocus (f : X ⟶ Y) :
    Set.InjOn f (f ⁻¹' (f.isoLocus : Set Y)) := by
  let U := f.isoLocus
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp le_rfl
  intro x hx y hy hxy
  let a : (f ⁻¹ᵁ U).toScheme := ⟨x, f.mem_preimage.mpr hx⟩
  let b : (f ⁻¹ᵁ U).toScheme := ⟨y, f.mem_preimage.mpr hy⟩
  have hab : (f ∣_ U) a = (f ∣_ U) b := Subtype.ext <|
    (morphismRestrict_base_coe f U a).trans (hxy.trans (morphismRestrict_base_coe f U b).symm)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective hab)

/-- The stalk map of a morphism at any point lying over its isomorphism locus is an isomorphism. -/
theorem isIso_stalkMap_of_mem_isoLocus (f : X ⟶ Y) {x : X}
    (hx : f x ∈ f.isoLocus) : IsIso (f.stalkMap x) := by
  let U := f.isoLocus
  let j := Scheme.Opens.ι (f ⁻¹ᵁ U)
  let xU : (f ⁻¹ᵁ U).toScheme := ⟨x, f.mem_preimage.mpr hx⟩
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp le_rfl
  have hiOpen : IsOpenImmersion (j ≫ f) := by
    rw [← morphismRestrict_ι f U]
    infer_instance
  have hi : IsIso ((j ≫ f).stalkMap xU) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hiOpen).2 xU
  have : IsIso (f.stalkMap (j xU) ≫ j.stalkMap xU) :=
    (Scheme.Hom.stalkMap_comp j f xU) ▸ hi
  exact IsIso.of_isIso_comp_right (f.stalkMap (j xU)) (j.stalkMap xU)

attribute [local instance] specializationOrder

/-- Codimension is preserved over the isomorphism locus of a morphism. -/
theorem coheight_eq_of_apply_mem_isoLocus (f : X ⟶ Y) {x : X} (hx : f x ∈ f.isoLocus) :
    Order.coheight (f x) = Order.coheight x := by
  let U := f.isoLocus
  let x' : (f ⁻¹ᵁ U).toScheme := ⟨x, f.mem_preimage.mpr hx⟩
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp le_rfl
  have : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by rw [← morphismRestrict_ι]; infer_instance
  have hι : (f ⁻¹ᵁ U).ι x' = x := (rfl)
  simpa only [Hom.comp_apply, hι] using
    (coheight_eq_of_isOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) (x := x')).trans
      (coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι (x := x')).symm

end AlgebraicGeometry.Scheme.Hom
