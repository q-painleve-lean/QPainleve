/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Two-dimensional cones in regular fans

In a rank-two regular fan, a cone with two rays is maximal among the cones of
the fan.
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

end Fan

end TauCeti.Toric
