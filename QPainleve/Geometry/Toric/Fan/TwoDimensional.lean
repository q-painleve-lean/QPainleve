/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Regular

import QPainleve.Geometry.Toric.Fan.Adjacency
import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Two-dimensional cones in regular fans

In a rank-two regular fan, a cone with two rays is maximal among the cones of
the fan. When the fan is complete, every cone is contained in one of these cones.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable {Φ : Fan i}

/-- A regular cone with two rays in a rank-two fan is maximal. -/
theorem eq_of_le_fullCone (hΦ : Φ.IsRegular) {σ τ : Φ.cones}
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) (h : σ ≤ τ) : σ = τ := by
  have hface := Φ.isFaceOf_of_le τ.property σ.property h
  have hτ := isRegular_iff.1 hΦ _ τ.property
  have := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  have := ToricRay.finite_of_fg hτ.fg
  let e := ToricRay.faceEmbedding hface
  let _ := Fintype.ofFinite (ToricRay σ.val)
  let _ := Fintype.ofFinite (ToricRay τ.val)
  have hcard : Fintype.card (ToricRay τ.val) ≤ Fintype.card (ToricRay σ.val) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc, ← hN]
    exact hτ.card_toricRay_le_finrank
  have hsurj := ((Fintype.bijective_iff_injective_and_card e).2
    ⟨e.injective, le_antisymm (Fintype.card_le_of_injective e e.injective) hcard⟩).2
  apply Subtype.ext
  refine le_antisymm h ?_
  rw [← (Φ.isToricCone τ.property).hull_primitiveGenerator Φ.lattice]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  obtain ⟨s, rfl⟩ := hsurj r
  rw [primitiveGenerator_faceEmbedding]
  exact s.val.isFaceOf.le (primitiveGenerator_mem Φ.lattice (Φ.isToricCone σ.property) s)

/-- A complete fan in a lattice with a nonzero vector has a ray. -/
theorem nonempty_ray_of_isComplete (Φ : Fan i) [Nontrivial N] (hc : Φ.IsComplete) :
    Nonempty Φ.Ray := by
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hix : i x ≠ 0 := fun h ↦ hx (Φ.lattice.injective (h.trans i.map_zero.symm))
  obtain ⟨σ, hσ, hmem⟩ := Φ.isComplete_iff.mp hc (i x)
  have hne : σ ≠ ⊥ := fun h ↦ hix (by simpa [h] using hmem)
  obtain ⟨ρ, -⟩ := Φ.exists_ray_le_of_ne_bot ⟨σ, hσ⟩ hne
  exact ⟨ρ⟩

/-- In a complete regular rank-two fan, every cone lies in a two-ray cone. -/
theorem exists_le_cone_of_card_toricRay_eq_two (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (σ : Φ.cones) :
    ∃ υ : Φ.cones, σ ≤ υ ∧ Nat.card (ToricRay υ.val) = 2 := by
  classical
  by_cases h : ∃ ρ τ : Φ.Ray, ρ ≠ τ ∧ ρ.toCone ≤ σ ∧ τ.toCone ≤ σ
  · obtain ⟨ρ, τ, hne, hρ, hτ⟩ := h
    exact ⟨σ, le_rfl, Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim hne hρ hτ⟩
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let b : Module.Basis (Fin 2) ℤ N := hdim ▸ Module.finBasis ℤ N
  have : Nontrivial N := Module.nontrivial_of_finrank_eq_succ (n := 1) hdim
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Φ.Ray, ∀ τ : Φ.Ray, τ.toCone ≤ σ → τ = ρ := by
    by_cases hs : ∃ ρ : Φ.Ray, ρ.toCone ≤ σ
    · obtain ⟨ρ, hρ⟩ := hs
      refine ⟨ρ, fun τ ht ↦ ?_⟩
      by_contra hne
      exact h ⟨τ, ρ, hne, ht, hρ⟩
    · obtain ⟨ρ⟩ := Φ.nonempty_ray_of_isComplete hc
      exact ⟨ρ, fun τ ht ↦ (hs ⟨τ, ht⟩).elim⟩
  obtain ⟨_, next, -, -, hneighbors⟩ := Φ.exists_ray_neighbors b hΦ hc ρ
  obtain ⟨hne, υ, hρυ, hnext⟩ := (hneighbors next).mpr (Or.inr rfl)
  refine ⟨υ, Φ.le_iff_forall_ray_le.mpr (fun τ hτ ↦ ?_),
    Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim hne hρυ hnext⟩
  rw [hρ τ hτ]
  exact hρυ

end Fan

end TauCeti.Toric
