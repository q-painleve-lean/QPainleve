/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Point
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Cone.TwoDimensional
import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Distinguished points in toric surface subdivisions

The image of a two-dimensional cone's distinguished point is the distinguished
point of its containing cone. A star subdivision lifts each such point to a
distinguished point of a two-dimensional cone, even at the node being blown up.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

/-- The subdivision projection takes the distinguished point of a two-ray
regular cone to the distinguished point of the cone containing it. -/
@[reassoc]
theorem IsSubdivision.distinguishedSection_comp_finiteFanSchemeHom_of_le_of_card_toricRay_eq_two
    (h : Φ.IsSubdivision Ψ) (hΦ : Φ.IsRegular) (hN : finrank ℤ N = 2)
    {σ : Φ.cones} {τ : Ψ.cones} (hσ : Nat.card (ToricRay σ.val) = 2) (hle : σ.val ≤ τ.val) :
    Φ.distinguishedSection (R := R) σ ≫ h.toFanHom.finiteFanSchemeHom R =
      Ψ.distinguishedSection (R := R) τ := by
  have hspan := ((isRegular_iff.mp hΦ) _ σ.property).span_eq_top_of_card_toricRay_eq_two
    Φ.lattice hN hσ
  apply h.toFanHom.distinguishedSection_comp_finiteFanSchemeHom_of_span_eq R σ τ
  · rw [h.toFanHom_realMap, LinearMap.id_coe]
    exact fun _ hx ↦ hle hx
  · rw [h.toFanHom_realMap, LinearMap.id_coe, Set.image_id, hspan]
    exact (top_unique (hspan ▸ Submodule.span_mono hle)).symm

/-- A two-ray star subdivision lifts every original corner to a corner in the
subdividing fan, including the corner at the center of the subdivision. -/
theorem IsTwoRayStarSubdivision.exists_lift_distinguishedSection
    (h : Φ.IsTwoRayStarSubdivision Ψ) (hN : finrank ℤ N = 2)
    (τ : Φ.cones) (hτ : Nat.card (ToricRay τ.val) = 2) :
    ∃ υ : Ψ.cones, Nat.card (ToricRay υ.val) = 2 ∧
      Ψ.distinguishedSection (R := R) υ ≫ h.isSubdivision.toFanHom.finiteFanSchemeHom R =
        Φ.distinguishedSection (R := R) τ := by
  cases h with
  | along hΦ σ hσ =>
    have hΨ := Φ.isRegular_starSubdivisionAlong hΦ σ.property
    have hex : ∃ υ : (Φ.starSubdivisionAlong hΦ σ.property).cones,
        Nat.card (ToricRay υ.val) = 2 ∧ υ.val ≤ τ.val := by
      by_cases hτσ : τ = σ
      · subst τ
        obtain ⟨e, b, hb⟩ := ((isRegular_iff.mp hΦ) _ σ.property).exists_basis_primitiveGenerators
          Φ.lattice hN hσ
        have hσshape := ((isRegular_iff.mp hΦ) _ σ.property).hull_eq_of_basis_primitiveGenerators
          Φ.lattice b e hb
        obtain ⟨c, hc₀, hc₁, hc⟩ := Φ.exists_starSubdivisionAlong_basis hΦ σ.property b
          (by simpa only [Set.range_comp] using hσshape.symm) 0
        refine ⟨⟨_, hc⟩, ?_, Submodule.span_le.mpr ?_⟩
        · let E := toricRayEquivOfLinearIndependent (i ∘ c)
            (Φ.lattice.linearIndependent_basis c) rfl
          rw [Nat.card_congr E, Nat.card_fin]
        · have hm (j : Fin 2) : i (b j) ∈ σ.val := by
            rw [hb]
            exact (e j).val.isFaceOf.le (primitiveGenerator_mem Φ.lattice _ (e j))
          have h0 : c 0 = b 0 + b 1 := hc₀
          have h1 : c 1 = b 1 := hc₁
          have hcj : ∀ j : Fin 2, i (c j) ∈ σ.val := Fin.forall_fin_two.mpr
            ⟨by rw [h0, map_add]; exact add_mem (hm 0) (hm 1), by rw [h1]; exact hm 1⟩
          rintro _ ⟨j, rfl⟩
          exact hcj j
      · have hnot : ¬ σ.val ≤ τ.val := fun hle ↦
          hτσ (Φ.eq_of_le_fullCone hΦ hN hσ hle).symm
        exact ⟨⟨_, Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property τ.property hnot⟩,
          hτ, le_rfl⟩
    obtain ⟨υ, hυ, hle⟩ := hex
    have hsub := (IsTwoRayStarSubdivision.along hΦ σ hσ).isSubdivision
    exact ⟨υ, hυ, hsub.distinguishedSection_comp_finiteFanSchemeHom_of_le_of_card_toricRay_eq_two
      R hΨ hN hυ hle⟩

end TauCeti.Toric.Fan
