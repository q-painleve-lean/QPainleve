/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import QPainleve.Geometry.Toric.BaseChange.FanMap
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import QPainleve.Geometry.Toric.BaseChange.ProjectiveSpace
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Noetherian

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

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
  {Φ Ψ : Fan i}

local notation "S" => Spec (CommRingCat.of k)

/-- A regular subdivision of a nonempty regular surface fan realizes a projective
scheme over the coefficient field exactly when the original fan does. -/
theorem IsSubdivision.isProjectiveOver_iff (h : Ψ.IsSubdivision Φ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΦ₀ : Nonempty Φ.cones) (hN : finrank ℤ N = 2) :
    (Ψ.finiteFanScheme k).IsProjectiveOver k ↔ (Φ.finiteFanScheme k).IsProjectiveOver k := by
  obtain ⟨n, Y, T, e, hT, he, -, -⟩ := h.exists_toric_subdivision_blowup_tower k hΦ hΨ hΦ₀ hN
  let : Nonempty Φ.cones := hΦ₀
  let : Y.Over S := ⟨T.toBase ≫ ((Φ.finiteFanScheme k) ↘ S)⟩
  let : e.hom.IsOver S := ⟨by
    change e.hom ≫ T.toBase ≫ Φ.finiteFanSchemeToSpec k = Ψ.finiteFanSchemeToSpec k
    rw [← Category.assoc, he, h.toFanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec k]⟩
  constructor
  · intro hproj
    let : (Ψ.finiteFanScheme k).IsProjectiveOver k := hproj
    let : e.inv.IsOver S := inferInstance
    let : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k) ↘ S) :=
      hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
    let : Smooth ((Φ.finiteFanScheme k) ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian (Φ.finiteFanScheme k) :=
      isNoetherian_of_finiteType ((Φ.finiteFanScheme k) ↘ S)
    have hY : Y.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k e.inv
    exact hT.isClosedPointTower.isProjectiveOver_base hY
  · intro hproj
    let : (Φ.finiteFanScheme k).IsProjectiveOver k := hproj
    let : Y.IsProjectiveOver k := T.isProjectiveOver k
    exact Scheme.IsProjectiveOver.of_isClosedImmersion k e.hom

/-- The scheme of a complete regular rank-two fan is projective over the coefficient field. -/
theorem isProjectiveOver_finiteFanScheme_of_isComplete (Φ : Fan i)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (b : Basis (Fin 2) ℤ N) :
    (Φ.finiteFanScheme k).IsProjectiveOver k := by
  let plane := projectiveSpace b Φ.lattice
  have hplane := isRegular_projectiveSpace b Φ.lattice
  have hcplane := isComplete_projectiveSpace b Φ.lattice
  have hN := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, hΩΦ, hΩplane, hΩ⟩ :=
    (FanEquiv.refl plane).exists_common_regular_subdivision_of_complete hΦ hplane hc hcplane b
  have hp : (plane.finiteFanScheme k).IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k (finiteFanSchemeToProjectiveSpace k b Φ.lattice)
  exact (hΩΦ.isProjectiveOver_iff k hΦ hΩ hc.nonempty_cones hN).mp
    ((hΩplane.isProjectiveOver_iff k hplane hΩ hcplane.nonempty_cones hN).mpr hp)

end TauCeti.Toric.Fan
