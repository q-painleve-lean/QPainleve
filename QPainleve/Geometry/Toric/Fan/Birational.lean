/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.PartialIso.DenseOpen
public import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Birational changes between toric fans on the same lattice

The common dense torus gives a specified partial isomorphism between the realizations
of two nonempty fans. Its rational map composes by changing the target fan, and for a
subdivision it agrees with the toric projection.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
  (Φ Ψ : Fan i) [Nonempty Φ.cones] [Nonempty Ψ.cones]

local notation "j[" A "]" => Fan.denseTorusι A inferInstance
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "s[" A "]" => Fan.algebraicRealizationStructureMap A

variable {Φ Ψ}

local notation "toricChange[" A ", " B "]" =>
  Scheme.PartialIso.ofDenseOpenImmersions (Fan.denseTorusι A inferInstance)
    (Fan.denseTorusι B inferInstance)

/-- A toric subdivision realizes the same-lattice birational change by a morphism. -/
@[simp]
theorem IsSubdivision.toRationalMap_algebraicMap (h : Φ.IsSubdivision Ψ) :
    h.toFanHom.algebraicMap.toRationalMap = toricChange[Φ, Ψ].toRationalMap := by
  apply Scheme.PartialIso.eq_toRationalMap_of_comp_ofDenseOpenImmersions
  rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
    h.denseTorusι_comp_algebraicMap]

/-- On a common subdivision, postcomposing either projection with the corresponding
toric change gives the other projection. This holds after any dominant morphism
from a preirreducible source to the common subdivision. -/
theorem IsSubdivision.comp_denseTorusPartialIso {Ω : Fan i} [Nonempty Ω.cones]
    (h : Ω.IsSubdivision Φ) (k : Ω.IsSubdivision Ψ) {Z : Scheme.{u}}
    [PreirreducibleSpace Z] (g : Z ⟶ X[Ω]) [IsDominant g] :
    (g ≫ h.toFanHom.algebraicMap).toRationalMap.comp toricChange[Φ, Ψ].toRationalMap =
      (g ≫ k.toFanHom.algebraicMap).toRationalMap := by
  calc
    _ = g.toRationalMap.comp
        (h.toFanHom.algebraicMap.toRationalMap.comp toricChange[Φ, Ψ].toRationalMap) := by
      rw [← Scheme.RationalMap.comp_assoc]
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
    _ = g.toRationalMap.comp toricChange[Ω, Ψ].toRationalMap := by
      simp only [h.toRationalMap_algebraicMap,
        Scheme.PartialIso.ofDenseOpenImmersions_toRationalMap_comp]
    _ = _ := by
      rw [← k.toRationalMap_algebraicMap, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom]

section Over

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ Ψ : Fan i) [Nonempty Φ.cones] [Nonempty Ψ.cones]

/-- The partial map of the toric change respects the structure maps. -/
instance : toricChange[Φ, Ψ].toPartialMap.IsOver s[Φ] s[Ψ] :=
  ⟨Scheme.PartialIso.ofDenseOpenImmersions_isOver j[Φ] j[Ψ] (by
    rw [Φ.denseTorusι_comp_structureMap, Ψ.denseTorusι_comp_structureMap])⟩

end Over

end TauCeti.Toric.Fan
