/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import Mathlib.AlgebraicGeometry.PullbackCarrier
import QPainleve.AlgebraicGeometry.Morphisms.Separated

/-!
# Isomorphism loci of scheme morphisms

For a surjective first map and a separated, universally closed second map with reduced
intermediate scheme, the centre of their composite is the union of the second centre and
the image of the first. Over its isomorphism locus, a morphism is injective, induces
isomorphisms on stalks, preserves codimension, and is quasi-finite. A regular source gives
regularity on the isomorphism locus. A dominant section over an open of the target of a
separated morphism with reduced source places that open in the isomorphism locus.
-/

public section

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- Precomposing with an isomorphism preserves the isomorphism locus. -/
theorem isoLocus_comp_of_isIso (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) :
    (f ≫ g).isoLocus = g.isoLocus := by
  apply le_antisymm
  · apply g.le_isoLocus_iff.mpr
    have : IsIso (f ∣_ g ⁻¹ᵁ (f ≫ g).isoLocus ≫ g ∣_ (f ≫ g).isoLocus) :=
      morphismRestrict_comp f g _ ▸ (f ≫ g).le_isoLocus_iff.mp le_rfl
    exact IsIso.of_isIso_comp_left (f ∣_ g ⁻¹ᵁ (f ≫ g).isoLocus) _
  · apply (f ≫ g).le_isoLocus_iff.mpr
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (inferInstance : IsIso (f ∣_ g ⁻¹ᵁ g.isoLocus))
      (g.le_isoLocus_iff.mp le_rfl)

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

/-- If two point sequences come from common lifts under `f` and `g`, a first
occurrence over the isomorphism loci of both maps is preserved after prepending
a point outside the isomorphism locus of `g` to the target sequence. -/
theorem first_occurrence_of_projected_points (f : X ⟶ Y) (g : X ⟶ Z) {n : ℕ}
    {sourcePoints : Fin n → Y} {targetPoints : Fin (1 + n) → Z}
    (hhead : targetPoints (Fin.castAdd n (0 : Fin 1)) ∉ g.isoLocus)
    (hlifts : ∀ k : Fin n, ∃ z : X,
      f z = sourcePoints k ∧ g z = targetPoints (k.natAdd 1))
    {z : X} (hs : f z ∈ f.isoLocus) (ht : g z ∈ g.isoLocus)
    (l : Fin n) (hl : sourcePoints l = f z)
    (hfirst : ∀ k < l, sourcePoints k ≠ f z) :
    targetPoints (l.natAdd 1) = g z ∧
      ∀ k < l.natAdd 1, targetPoints k ≠ g z := by
  obtain ⟨u, hu, hu'⟩ := hlifts l
  have hproj := hu.trans hl
  have hpt : u = z := f.injOn_preimage_isoLocus
    (by rwa [Set.mem_preimage, hproj]) hs hproj
  refine ⟨hu'.symm.trans (congrArg g hpt), ?_⟩
  refine Fin.addCases ?_ ?_
  · intro k _ he
    rw [Subsingleton.elim k (0 : Fin 1)] at he
    exact hhead (he ▸ ht)
  · intro k hk he
    obtain ⟨w, hw, hw'⟩ := hlifts k
    have hproj' := hw'.trans he
    have hpt' := g.injOn_preimage_isoLocus
      (by rwa [Set.mem_preimage, hproj']) ht hproj'
    exact hfirst k (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hk)
      (hw.symm.trans (congrArg f hpt'))

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

/-- With regular source, regularity of the target can be checked at the points of the centre. -/
theorem isRegular_of_isRegularLocalRing_of_mem_centre (f : X ⟶ Y)
    [IsRegular X] [IsLocallyNoetherian Y]
    (h : ∀ y ∈ f.centre, IsRegularLocalRing (Y.presheaf.stalk y)) : IsRegular Y := by
  refine ⟨fun y ↦ ?_⟩
  by_cases hy : y ∈ f.centre
  · exact h y hy
  · have hy' : y ∈ f.isoLocus := by simpa only [centre_def, Set.mem_compl_iff, not_not,
      SetLike.mem_coe] using hy
    obtain ⟨x, hx⟩ := (f ∣_ f.isoLocus).surjective ⟨y, hy'⟩
    have hxy : f x.val = y :=
      (morphismRestrict_base_coe f f.isoLocus x).symm.trans (congrArg Subtype.val hx)
    have := f.isIso_stalkMap_of_mem_isoLocus (x := x.val) (hxy.symm ▸ hy')
    exact hxy ▸ IsRegularLocalRing.of_ringEquiv
      (asIso (f.stalkMap x.val)).commRingCatIsoToRingEquiv.symm

section

variable (f : X ⟶ Y)

/-- A dominant morphism from an open of the target giving a section there places that open
inside the isomorphism locus. -/
theorem le_isoLocus_of_dominant_section [IsReduced X] [IsSeparated f]
    {U : Y.Opens} (s : U.toScheme ⟶ X) [IsDominant s] (hs : s ≫ f = U.ι) :
    U ≤ f.isoLocus := by
  let H := (isPullback_morphismRestrict f U).flip
  let t := H.lift s (𝟙 U.toScheme) (by simpa using hs)
  have ht : t ≫ (f ⁻¹ᵁ U).ι = s := H.lift_fst _ _ _
  have : IsDominant (t ≫ (f ⁻¹ᵁ U).ι) := ht.symm ▸ inferInstanceAs (IsDominant s)
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (f ⁻¹ᵁ U).ι
  exact f.le_isoLocus_iff.mpr <|
    (f ∣_ U).isIso_of_dominant_section t (H.lift_snd _ _ _)

/-- A morphism is quasi-finite at each point above its isomorphism locus. -/
theorem quasiFiniteAt_of_mem_isoLocus {x : X}
    (hx : f x ∈ f.isoLocus) : f.QuasiFiniteAt x := by
  let V := f.isoLocus
  let z : f ⁻¹ᵁ V := ⟨x, hx⟩
  have h : LocallyQuasiFinite ((f ⁻¹ᵁ V).ι ≫ f) :=
    (morphismRestrict_ι f V) ▸ inferInstanceAs (LocallyQuasiFinite ((f ∣_ V) ≫ V.ι))
  exact (quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (f ⁻¹ᵁ V).ι) (g := f)
    (x := z)).mp (((f ⁻¹ᵁ V).ι ≫ f).quasiFiniteAt z)

end

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
