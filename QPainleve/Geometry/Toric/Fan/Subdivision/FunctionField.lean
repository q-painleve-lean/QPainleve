/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.FunctionField
public import QPainleve.Geometry.Toric.Fan.Subdivision.Basic

import QPainleve.AlgebraicGeometry.Scheme.FunctionField

/-!
# Function fields under subdivision

A subdivision induces the identity on the common dense torus. Its morphism of toric
schemes is therefore dominant and its pullback on function fields is an isomorphism.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

variable [hΦ : Nonempty Φ.cones] [hΨ : Nonempty Ψ.cones]

local notation "hbotΦ" => Fan.bot_mem Φ (Subtype.property (Nonempty.some hΦ))
local notation "hbotΨ" => Fan.bot_mem Ψ (Subtype.property (Nonempty.some hΨ))

/-- A subdivision of nonempty fans induces a dominant morphism of toric schemes. -/
instance isDominant_finiteFanSchemeHom : IsDominant (h.toFanHom.finiteFanSchemeHom R) := by
  let j := Φ.affineChartι R ⟨⊥, hbotΦ⟩
  have : IsDominant (j ≫ h.toFanHom.finiteFanSchemeHom R) := by
    rw [h.affineChartι_comp_finiteFanSchemeHom R hbotΦ hbotΨ]
    infer_instance
  exact IsDominant.of_comp j _

variable [IsDomain R]

/-- A subdivision of nonempty fans induces an isomorphism on function fields. -/
instance isIso_functionFieldMap : IsIso (h.toFanHom.finiteFanSchemeHom R).functionFieldMap := by
  let j := Φ.affineChartι R ⟨⊥, hbotΦ⟩
  apply IsIso.of_isIso_fac_right (f := j.functionFieldMap)
    (h := (Ψ.affineChartι R ⟨⊥, hbotΨ⟩).functionFieldMap)
  rw [← Scheme.Hom.functionFieldMap_comp]
  exact Scheme.Hom.functionFieldMap_congr (h.affineChartι_comp_finiteFanSchemeHom R _ _)

end TauCeti.Toric.Fan.IsSubdivision
