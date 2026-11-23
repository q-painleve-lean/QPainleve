/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.FunctionField

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

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)

variable [Nonempty Φ.cones] [Nonempty Ψ.cones]

/-- A subdivision of nonempty fans induces a dominant morphism of toric schemes. -/
instance isDominant_algebraicMap : IsDominant h.toFanHom.algebraicMap := by
  let j := Φ.denseTorusι inferInstance
  have : IsDominant (j ≫ h.toFanHom.algebraicMap) := by
    rw [h.denseTorusι_comp_algebraicMap inferInstance inferInstance]
    infer_instance
  exact IsDominant.of_comp j _

/-- A subdivision of nonempty fans induces an isomorphism on function fields. -/
instance isIso_functionFieldMap : IsIso h.toFanHom.algebraicMap.functionFieldMap := by
  let j := Φ.denseTorusι inferInstance
  apply IsIso.of_isIso_fac_right (f := j.functionFieldMap)
    (h := (Ψ.denseTorusι inferInstance).functionFieldMap)
  rw [← Scheme.Hom.functionFieldMap_comp]
  exact Scheme.Hom.functionFieldMap_congr (h.denseTorusι_comp_algebraicMap _ _)

end TauCeti.Toric.Fan.IsSubdivision
