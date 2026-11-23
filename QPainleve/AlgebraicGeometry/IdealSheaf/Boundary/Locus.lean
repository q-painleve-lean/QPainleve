/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Local properties of the reduced boundary

Properties of boundary points that are detected on open neighborhoods can be compared
after restricting the ambient scheme. In particular, smooth points and nodes of the reduced
boundary are transported over the isomorphism locus of the ambient comparison.
-/

public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y S : Scheme.{u}}

section LocalProperty

variable (P : ∀ {Z : Scheme.{u}}, (Z ⟶ S) → Z → Prop)
  (hP : ∀ {A B : Scheme.{u}} (g : B ⟶ S) (f : A ⟶ B) [IsOpenImmersion f] (a : A),
    P (f ≫ g) a ↔ P g (f a))

include hP

/-- An open-local property on the reduced boundary agrees with that of its inverse image
under an open immersion. -/
theorem exists_reducedBoundaryPoint_comap_iff_of_isOpenImmersion
    (D : Y.IdealSheafData) (g : Y ⟶ S) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (∃ z : (D.comap f).radical.subscheme, (D.comap f).radical.subschemeι z = x ∧
      P ((D.comap f).radical.subschemeι ≫ f ≫ g) z) ↔
    ∃ z : D.radical.subscheme, D.radical.subschemeι z = f x ∧ P (D.radical.subschemeι ≫ g) z := by
  rw [D.radical_comap_of_isOpenImmersion f]
  let I := D.radical
  let J := I.comap f
  let c := subschemeMap J I f (I.le_map_comap f)
  have H : IsPullback J.subschemeι c f I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [c]) (by simp [J])
  have : IsOpenImmersion c := MorphismProperty.of_isPullback H inferInstance
  have happ (z : J.subscheme) : I.subschemeι (c z) = f (J.subschemeι z) := by
    simpa only [← Scheme.Hom.comp_apply] using congrArg (fun m : J.subscheme ⟶ Y ↦ m z) H.w.symm
  have hpoint (z : J.subscheme) :
      P (J.subschemeι ≫ f ≫ g) z ↔ P (I.subschemeι ≫ g) (c z) := by
    rw [H.w_assoc]
    exact hP _ c z
  constructor
  · rintro ⟨z, rfl, hz⟩
    exact ⟨c z, happ z, (hpoint z).mp hz⟩
  · rintro ⟨z, hz, hprop⟩
    have hx : x ∈ Set.range J.subschemeι := by
      rw [Scheme.Pullback.range_fst_of_isPullback H]
      exact ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := hx
    have hw : c w = z := I.subschemeι.isClosedEmbedding.injective ((happ w).trans hz.symm)
    exact ⟨w, rfl, (hpoint w).mpr (hw.symm ▸ hprop)⟩

/-- An open-local property on the reduced boundary agrees with that of its inverse image
at a point over the isomorphism locus. -/
theorem exists_reducedBoundaryPoint_comap_iff_of_mem_isoLocus
    (D : Y.IdealSheafData) (g : Y ⟶ S) (f : X ⟶ Y) {x : X} (hx : f x ∈ f.isoLocus) :
    (∃ z : (D.comap f).radical.subscheme, (D.comap f).radical.subschemeι z = x ∧
      P ((D.comap f).radical.subschemeι ≫ f ≫ g) z) ↔
    ∃ z : D.radical.subscheme, D.radical.subschemeι z = f x ∧ P (D.radical.subschemeι ≫ g) z := by
  let U := f.isoLocus
  let j := (f ⁻¹ᵁ U).ι
  let z : (f ⁻¹ᵁ U).toScheme := ⟨x, f.mem_preimage.mpr hx⟩
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp le_rfl
  have : IsOpenImmersion (j ≫ f) := by
    rw [← morphismRestrict_ι f U]
    infer_instance
  have h₁ := exists_reducedBoundaryPoint_comap_iff_of_isOpenImmersion P hP (D.comap f) (f ≫ g) j z
  have h₂ := exists_reducedBoundaryPoint_comap_iff_of_isOpenImmersion P hP D g (j ≫ f) z
  rw [comap_comp, Category.assoc, Scheme.Hom.comp_apply] at h₂
  exact h₁.symm.trans h₂

end LocalProperty

/-- The ambient points where the reduced boundary is formally smooth over the base.
For a boundary locally of finite presentation over the base this is the smooth locus
of the boundary, viewed in the ambient scheme. -/
def smoothBoundaryPoints (D : Y.IdealSheafData) (g : Y ⟶ S) : Set Y :=
  {x | ∃ z : D.radical.subscheme, D.radical.subschemeι z = x ∧
    ((D.radical.subschemeι ≫ g).stalkMap z).hom.FormallySmooth}

/-- The smooth points of the reduced boundary are unchanged by reducing its ideal. -/
@[simp]
theorem smoothBoundaryPoints_radical (D : Y.IdealSheafData) (g : Y ⟶ S) :
    D.radical.smoothBoundaryPoints g = D.smoothBoundaryPoints g := by
  have hD : IsReduced D.radical.subscheme := by
    rw [← vanishingIdeal_support]
    infer_instance
  unfold smoothBoundaryPoints
  rw [(D.radical.isReduced_subscheme_iff_radical_eq).mp hD]

/-- An ambient point is smooth on the reduced boundary when the stalk map at the
point over it is formally smooth. -/
theorem mem_smoothBoundaryPoints_iff (D : Y.IdealSheafData) (g : Y ⟶ S) (x : Y) :
    x ∈ D.smoothBoundaryPoints g ↔
      ∃ z : D.radical.subscheme, D.radical.subschemeι z = x ∧
        ((D.radical.subschemeι ≫ g).stalkMap z).hom.FormallySmooth := (Iff.rfl)

/-- Membership in the smooth locus of the reduced boundary can be checked at its
unique point over the given ambient point. -/
theorem mem_smoothBoundaryPoints_iff_mem_smoothLocus (D : Y.IdealSheafData) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (D.radical.subschemeι ≫ g)] (x : Y) :
    x ∈ D.smoothBoundaryPoints g ↔
      ∃ z : D.radical.subscheme, D.radical.subschemeι z = x ∧
        z ∈ (D.radical.subschemeι ≫ g).smoothLocus := by
  simp only [mem_smoothBoundaryPoints_iff, Scheme.Hom.mem_smoothLocus]

/-- Smooth points of the reduced boundary lie on its support. -/
theorem smoothBoundaryPoints_subset_support (D : Y.IdealSheafData) (g : Y ⟶ S) :
    D.smoothBoundaryPoints g ⊆ D.support := by
  rintro x ⟨z, rfl, _⟩
  rw [← support_radical, ← range_subschemeι]
  exact Set.mem_range_self z

/-- Over the isomorphism locus of an ambient map, smooth points of the reduced
inverse image are exactly the points lying over smooth points of the reduced boundary. -/
theorem mem_smoothBoundaryPoints_comap_iff_of_mem_isoLocus
    (D : Y.IdealSheafData) (g : Y ⟶ S) (f : X ⟶ Y) {x : X} (hx : f x ∈ f.isoLocus) :
    x ∈ (D.comap f).smoothBoundaryPoints (f ≫ g) ↔ f x ∈ D.smoothBoundaryPoints g :=
  exists_reducedBoundaryPoint_comap_iff_of_mem_isoLocus
    (fun {_} q z ↦ (q.stalkMap z).hom.FormallySmooth)
    (fun g' f' _ z ↦
      RingHom.FormallySmooth.respectsIso.stalkMap_comp_isOpenImmersion_iff f' g' z)
    D g f hx

end AlgebraicGeometry.Scheme.IdealSheafData
