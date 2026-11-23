/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.FaceLocalization
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# Density of the torus in a toric scheme

The inclusion of a face induces an injective map of affine toric coordinate rings, so
the corresponding open immersion is dominant. Applying this to the zero face in each
chart shows that Tau Ceti's torus inclusion is dense in any nonempty fan realization.
The zero-cone subfan also identifies the inverse image of the torus under a subdivision.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The torus inclusion in the scheme of a nonempty fan is dominant. -/
instance isDominant_denseTorusι (Φ : Fan i) (hΦ : Nonempty Φ.cones) :
    IsDominant (Φ.denseTorusι hΦ) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  let hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  have hdense := (isDominant_faceAffineToricSchemeMap Φ.lattice hface).denseRange
  have hclosure := (Φ.affineToricChartι σ).continuous.range_subset_closure_image_dense hdense
  have hcomp : ⇑(faceAffineToricSchemeMap Φ.lattice hface ≫ Φ.affineToricChartι σ) =
      ⇑(Φ.affineToricChartι σ) ∘ ⇑(faceAffineToricSchemeMap Φ.lattice hface) :=
    funext (Scheme.Hom.comp_apply _ _)
  rw [← Set.range_comp, ← hcomp, ← Φ.denseTorusι_face σ] at hclosure
  exact hclosure ⟨y, rfl⟩

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan.IsSubdivision

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

end TauCeti.Toric.Fan.IsSubdivision
