/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Translation

/-!
# Torus translations on fan subdivisions

The map of toric schemes induced by a subdivision commutes with translations
by a point of the common dense torus.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Δ Ψ : Fan i}

/-- A torus translation before a subdivision morphism agrees with translation
by the same torus point after that morphism. -/
@[reassoc]
theorem torusTranslationIso_hom_comp_finiteFanSchemeHom (H : Δ.IsSubdivision Ψ)
    (χ : Multiplicative (N →+ ℤ) →* Rˣ) :
    (Δ.torusTranslationIso R χ).hom ≫ H.toFanHom.finiteFanSchemeHom R =
      H.toFanHom.finiteFanSchemeHom R ≫ (Ψ.torusTranslationIso R χ).hom := by
  apply Δ.finiteFanScheme_hom_ext R
  intro σ
  let f := H.toFanHom
  let τ : Ψ.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  have hmaps : Set.MapsTo f.realMap (σ.val : Set V) (τ.val : Set V) :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  change Δ.affineChartι R σ ≫ (Δ.torusTranslationIso R χ).hom ≫ f.finiteFanSchemeHom R =
    Δ.affineChartι R σ ≫ f.finiteFanSchemeHom R ≫ (Ψ.torusTranslationIso R χ).hom
  rw [Δ.affineChartι_comp_torusTranslationIso_hom_assoc R χ σ,
    f.affineChartι_comp_finiteFanSchemeHom R σ τ hmaps,
    f.affineChartι_comp_finiteFanSchemeHom_assoc R σ τ hmaps,
    Ψ.affineChartι_comp_torusTranslationIso_hom R χ τ, affineChartMap_def,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  let a := mapDomainAlgHom R R (dualSemigroupMap Δ.lattice Ψ.lattice
    f.latticeMap f.realMap f.map_lattice hmaps)
  let tσ := (charTwist (χ.comp (dualSemigroup Δ.lattice σ.val).subtype.toMultiplicative)).toAlgHom
  let tτ := (charTwist (χ.comp (dualSemigroup Ψ.lattice τ.val).subtype.toMultiplicative)).toAlgHom
  change (tσ.comp a).toRingHom = (a.comp tτ).toRingHom
  apply congrArg AlgHom.toRingHom
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    simp [a, tσ, tτ, f, AddMonoidAlgebra.charTwist_single, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
  · exact Subsingleton.elim _ _

end TauCeti.Toric.Fan.IsSubdivision
