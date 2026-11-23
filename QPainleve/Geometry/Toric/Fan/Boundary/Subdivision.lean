/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# The boundary under a fan subdivision

The inverse image of the dense torus under a subdivision is the dense torus.
Consequently the reduced inverse image of the toric boundary is the toric
boundary of the subdividing fan. The zero-cone subfan gives the torus via
`FanHom.range_preimageSubfanAlgebraicMap`.
-/

public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  (hΦ : Nonempty Φ.cones) (hΨ : Nonempty Ψ.cones)

private theorem range_subfanInclusion_algebraicMap_of_eq_singleton_bot
    (A : Fan i) (hA : Nonempty A.cones) {T : Set (PointedCone ℝ V)}
    (hT : T ⊆ A.cones) (hface : ∀ ⦃σ τ⦄, σ ∈ T → τ.IsFaceOf σ → τ ∈ T)
    (heq : T = {⊥}) :
    Set.range (A.subfanInclusion T hT hface).algebraicMap = Set.range (A.denseTorusι hA) := by
  have hbot : (⊥ : PointedCone ℝ V) ∈ T := heq.symm ▸ Set.mem_singleton _
  rw [A.range_subfanInclusion_algebraicMap T hT hface,
    A.denseTorusι_eq_affineToricChartι hA (hT hbot)]
  refine le_antisymm (iSup_le fun σ ↦ ?_) (le_iSup_of_le ⟨⊥, ?_⟩ le_rfl)
  · have hσ : σ.val ∈ T := by simpa only [subfan_cones] using σ.property
    exact le_of_eq (congrArg (fun τ : A.cones ↦ Set.range (A.affineToricChartι τ))
      (Subtype.ext (Set.mem_singleton_iff.mp (heq ▸ hσ))))
  · simpa only [subfan_cones] using hbot

/-- A subdivision pulls back the open dense torus to the open dense torus. -/
theorem preimage_range_denseTorusι :
    h.toFanHom.algebraicMap ⁻¹' Set.range (Ψ.denseTorusι hΨ) =
      Set.range (Φ.denseTorusι hΦ) := by
  let T : Set (PointedCone ℝ V) := {⊥}
  have hbΦ : (⊥ : PointedCone ℝ V) ∈ Φ.cones := let ⟨σ⟩ := hΦ; Φ.bot_mem σ.property
  have hbΨ : (⊥ : PointedCone ℝ V) ∈ Ψ.cones := let ⟨σ⟩ := hΨ; Ψ.bot_mem σ.property
  have hT : T ⊆ Ψ.cones := Set.singleton_subset_iff.mpr hbΨ
  have hface : ∀ ⦃σ τ⦄, σ ∈ T → τ.IsFaceOf σ → τ ∈ T := by
    intro σ τ hσ hτ
    exact Set.mem_singleton_iff.mpr (le_bot_iff.mp (Set.mem_singleton_iff.mp hσ ▸ hτ.le))
  have hp : h.toFanHom.preimageCones T = {⊥} := by
    ext σ
    rw [Set.mem_singleton_iff]
    constructor
    · intro hσ
      have hσΦ := h.toFanHom.preimageCones_subset T hσ
      have hleast := (h.toFanHom.mem_preimageCones_iff T hσΦ).mp hσ
      exact le_bot_iff.mp ((h.le_leastCone hσΦ).trans_eq (Set.mem_singleton_iff.mp hleast))
    · rintro rfl
      refine (h.toFanHom.mem_preimageCones_iff T hbΦ).mpr ?_
      rw [h.leastCone_eq_self hbΦ hbΨ]
      exact Set.mem_singleton _
  rw [← range_subfanInclusion_algebraicMap_of_eq_singleton_bot Ψ hΨ hT hface rfl,
    ← h.toFanHom.range_preimageSubfanAlgebraicMap T hT hface]
  exact range_subfanInclusion_algebraicMap_of_eq_singleton_bot Φ hΦ _ _ hp

/-- The reduced inverse image of the toric boundary is the boundary of the subdivision. -/
theorem radical_comap_boundaryIdeal :
    ((Ψ.boundaryIdeal hΨ).comap h.toFanHom.algebraicMap).radical = Φ.boundaryIdeal hΦ := by
  rw [← vanishingIdeal_support, Φ.boundaryIdeal_def]
  congr 1
  apply SetLike.coe_injective
  rw [support_comap, Closeds.coe_preimage, Ψ.support_boundaryIdeal,
    Set.preimage_compl, h.preimage_range_denseTorusι hΦ hΨ]
  rfl

end TauCeti.Toric.Fan.IsSubdivision
