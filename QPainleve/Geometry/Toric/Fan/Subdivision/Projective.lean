/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.FunctionField
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj

/-!
# Projectivity of regular toric surfaces

A regular subdivision of a surface fan preserves and reflects projectivity
because its projection is an ordered tower of point blowups. Comparing with
the plane fan on a common regular subdivision gives projectivity for complete
regular surface fans.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ Ψ : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)

/-- A regular subdivision of a nonempty regular surface fan realizes a projective
scheme over `ℂ` exactly when the original fan does. -/
theorem IsSubdivision.isProjectiveOver_iff (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΦ₀ : Nonempty Φ.cones) (hN : finrank ℤ N = 2) :
    Ψ.algebraicRealization.IsProjectiveOver ℂ ↔ Φ.algebraicRealization.IsProjectiveOver ℂ := by
  obtain ⟨n, Y, T, e, hT, he, -, -⟩ := h.exists_toric_subdivision_blowup_tower hΦ hΨ hΦ₀ hN
  let : Nonempty Φ.cones := hΦ₀
  let : Y.Over S := ⟨T.toBase ≫ (Φ.algebraicRealization ↘ S)⟩
  let : e.hom.IsOver S :=
    ⟨((reassoc_of% he) (Φ.algebraicRealization ↘ S)).trans
      h.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap⟩
  constructor
  · intro hproj
    let : Ψ.algebraicRealization.IsProjectiveOver ℂ := hproj
    let : e.inv.IsOver S := inferInstance
    let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) :=
      hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : Smooth (Φ.algebraicRealization ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian Φ.algebraicRealization :=
      isNoetherian_of_finiteType (Φ.algebraicRealization ↘ S)
    have hY : Y.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.inv
    exact hT.isClosedPointTower.isProjectiveOver_base hY
  · intro hproj
    let : Φ.algebraicRealization.IsProjectiveOver ℂ := hproj
    let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
    exact Scheme.IsProjectiveOver.of_isClosedImmersion ℂ e.hom

/-- The scheme of a complete regular rank-two fan is projective over `ℂ`. -/
theorem isProjectiveOver_algebraicRealization_of_isComplete (Φ : Fan i)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Basis (Fin 2) ℤ N) :
    Φ.algebraicRealization.IsProjectiveOver ℂ := by
  let plane := projectiveSpace b Φ.lattice
  have hplane := isRegular_projectiveSpace b Φ.lattice
  have hcplane := isComplete_projectiveSpace b Φ.lattice
  have hN := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, hΩΦ, hΩplane, hΩ⟩ :=
    (FanEquiv.refl plane).exists_common_regular_subdivision_of_complete hΦ hplane hc hcplane b
  have hp : plane.algebraicRealization.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (projectiveSpaceToProj b Φ.lattice)
  exact (hΩΦ.isProjectiveOver_iff hΦ hΩ hc.nonempty_cones hN).mp
    ((hΩplane.isProjectiveOver_iff hplane hΩ hcplane.nonempty_cones hN).mpr hp)

end TauCeti.Toric.Fan
