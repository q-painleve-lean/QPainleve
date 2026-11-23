/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

/-!
# Nonempty fan subdivisions

The subdivision of a nonempty fan again has a cone. This supplies the
nonemptiness needed for constructions such as the dense torus and its boundary.
-/

public section

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

/-- A subdivision of a nonempty fan is nonempty. -/
theorem nonempty_cones_of_nonempty (h : Φ.IsSubdivision Ψ) (hΨ : Nonempty Ψ.cones) :
    Nonempty Φ.cones := by
  obtain ⟨σ⟩ := hΨ
  obtain ⟨τ, hτ, -, -⟩ := h.exists_mem_cone σ.property (zero_mem σ.val)
  exact ⟨⟨τ, hτ⟩⟩

end TauCeti.Toric.Fan.IsSubdivision
