/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.SectionDivision
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.RationalMap
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
import QPainleve.AlgebraicGeometry.LineBundle.NonvanishingLocus
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Comparison
import QPainleve.AlgebraicGeometry.RationalMap.Composition
import TauCeti.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Extending projective rational maps with Cartier base ideal

Dividing a projective presentation by its effective Cartier base ideal gives
coordinates that generate everywhere. The resulting morphism over the base
represents the given rational map. This is the projective extension step in
the resolution of base points by principalizing a linear system.

See [Stacks Project, Section 27.13](https://stacks.math.columbia.edu/tag/01ND)
for the construction of projective morphisms from generating sections.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.MvPolynomial

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [IsIntegral X] {R ι : Type u} [CommRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

private theorem exists_projective_morphism_with_cartier_twist
    (L : InvertibleSheaf X) (f : X ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (Scheme.Modules.nonvanishingLocus L.obj (s i) : Set X))
    (hI : (⨆ j, L.zeroIdeal (s j)).IsEffectiveCartier) :
    ∃ g : X ⟶ Proj 𝒜, g ≫ Proj.toSpecCoeff 𝒜 = f ∧
      g.toRationalMap =
        (Scheme.Modules.partialMapToProjectiveSpace L.obj f s i hi).toRationalMap ∧
      ∃ e : (Scheme.Modules.pullback g).obj (Proj.twistingSheaf 𝒜 1) ≅
          (hI.toInvertibleSheaf.tensorProduct L).obj,
        ∀ j, (L.idealTwistInclusion hI).app ⊤
          (e.hom.app ⊤ (g.pullbackSections (Proj.twistingSheaf 𝒜 1) ⊤
            (Proj.polynomialCoordinateSection j))) = s j := by
  obtain ⟨t, ht, hcover⟩ := L.exists_idealTwist_sections_of_cartier_base_ideal s hI
  let K := hI.toInvertibleSheaf.tensorProduct L
  obtain ⟨x, hx⟩ := hi.nonempty
  have hs : s i ≠ 0 := (L.genericPoint_mem_nonvanishingLocus_iff _).mp
    ((genericPoint_specializes x).mem_open (Scheme.Modules.nonvanishingLocus L.obj (s i)).isOpen hx)
  have ht_ne : t i ≠ 0 := by
    intro h
    apply hs
    rw [← ht i, h, map_zero]
  have hd : Dense (Scheme.Modules.nonvanishingLocus K.obj (t i) : Set X) :=
    (Scheme.Modules.nonvanishingLocus K.obj (t i)).isOpen.dense
      ⟨genericPoint X, (K.genericPoint_mem_nonvanishingLocus_iff _).mpr ht_ne⟩
  let g := Scheme.Modules.toProjectiveSpace K.obj f t hcover
  have hg : g ≫ Proj.toSpecCoeff 𝒜 = f :=
    Scheme.Modules.toProjectiveSpace_toSpecCoeff K.obj f t hcover
  have heq : g.toRationalMap =
      (Scheme.Modules.partialMapToProjectiveSpace L.obj f s i hi).toRationalMap :=
    (Scheme.Modules.toRationalMap_partialMapToProjectiveSpace K.obj f t hcover i hd).symm.trans
      (Scheme.Modules.toRationalMap_partialMapToProjectiveSpace_eq_of_hom f t s
        (L.idealTwistInclusion hI) ht i hd hi)
  obtain ⟨e, he⟩ := K.obj.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f t hcover
  exact ⟨g, hg, heq, e, fun j ↦ (congrArg ((L.idealTwistInclusion hI).app ⊤) (he j)).trans (ht j)⟩

/-- A projective presentation with effective Cartier base ideal extends to a unique
morphism over the base, agreeing with the given presentation as a rational map. -/
theorem exists_projective_morphism_of_cartier_base_ideal
    (L : InvertibleSheaf X) (f : X ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (Scheme.Modules.nonvanishingLocus L.obj (s i) : Set X))
    (hI : (⨆ j, L.zeroIdeal (s j)).IsEffectiveCartier) :
    ∃! g : X ⟶ Proj 𝒜, g ≫ Proj.toSpecCoeff 𝒜 = f ∧
      g.toRationalMap =
        (Scheme.Modules.partialMapToProjectiveSpace L.obj f s i hi).toRationalMap := by
  obtain ⟨g, hg, heq, -⟩ := L.exists_projective_morphism_with_cartier_twist f s i hi hI
  let : (Proj 𝒜).IsSeparated := Scheme.IsSeparated.of_isSeparated (Proj.toSpecCoeff 𝒜)
  exact ⟨g, ⟨hg, heq⟩, fun g' hg' ↦ Scheme.Hom.toRationalMap_injective (hg'.2.trans heq.symm)⟩

/-- On a regular representative of a projective presentation with Cartier base ideal,
the pullback of `𝒪(1)` is the presenting line bundle twisted by the base ideal. Under
the twist inclusion the pulled-back coordinates are the original sections. -/
theorem exists_iso_pullbackTwistingSheaf_of_cartier_base_ideal
    (L : InvertibleSheaf X) (f : X ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (Scheme.Modules.nonvanishingLocus L.obj (s i) : Set X))
    (hI : (⨆ j, L.zeroIdeal (s j)).IsEffectiveCartier) (g : X ⟶ Proj 𝒜)
    (hg : g.toRationalMap =
      (Scheme.Modules.partialMapToProjectiveSpace L.obj f s i hi).toRationalMap) :
    ∃ e : (Scheme.Modules.pullback g).obj (Proj.twistingSheaf 𝒜 1) ≅
        (hI.toInvertibleSheaf.tensorProduct L).obj,
      ∀ j, (L.idealTwistInclusion hI).app ⊤
        (e.hom.app ⊤ (g.pullbackSections (Proj.twistingSheaf 𝒜 1) ⊤
          (Proj.polynomialCoordinateSection j))) = s j := by
  obtain ⟨g', -, hg', he⟩ := L.exists_projective_morphism_with_cartier_twist f s i hi hI
  let : (Proj 𝒜).IsSeparated := Scheme.IsSeparated.of_isSeparated (Proj.toSpecCoeff 𝒜)
  have h : g = g' := Scheme.Hom.toRationalMap_injective (hg.trans hg'.symm)
  exact h.symm ▸ he

end TauCeti.AlgebraicGeometry.InvertibleSheaf
