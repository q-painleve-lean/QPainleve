/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation
public import QPainleve.Geometry.Toric.Fan.DenseTorus

import QPainleve.Geometry.Toric.Fan.Separated

/-!
# Torus translations on fan subdivisions

The map of toric schemes induced by a subdivision commutes with translations
by a point of the common dense torus.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Δ Ψ : Fan i} [Nonempty Δ.cones] [Nonempty Ψ.cones]

/-- A torus translation before a subdivision morphism agrees with translation
by the same torus point after that morphism. -/
@[reassoc]
theorem torusTranslation_hom_comp_algebraicMap (H : Δ.IsSubdivision Ψ)
    (χ : Multiplicative (N →+ ℤ) →* ℂˣ) :
    (Δ.torusTranslation χ).hom ≫ H.toFanHom.algebraicMap =
      H.toFanHom.algebraicMap ≫ (Ψ.torusTranslation χ).hom := by
  apply AlgebraicGeometry.ext_of_isDominant (Δ.denseTorusι inferInstance)
  have h := H.denseTorusι_comp_algebraicMap inferInstance inferInstance
  rw [reassoc_of% h, Ψ.denseTorusι_comp_torusTranslation_hom,
    ← Category.assoc, Δ.denseTorusι_comp_torusTranslation_hom, Category.assoc, h]

end TauCeti.Toric.Fan.IsSubdivision
