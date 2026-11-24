/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray

import QPainleve.Geometry.Toric.Fan.HalfPlane

/-!
# The ruling character of a Hirzebruch fan

The opposite rays along the first basis direction are in the kernel of the second
coordinate character. This gives the cone-wise sign condition for the ruling.
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)

include hr in
/-- The second coordinate character has constant weak sign on each cone of a
Hirzebruch fan, so it defines the ruling to the projective line. -/
theorem nonneg_or_nonpos_hirzebruch_ruling_character (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0 := by
  have h₀ : (r 0).primitiveGenerator = b 0 := congrFun hr 0
  have h₂ : (r 2).primitiveGenerator = -b 0 := congrFun hr 2
  have hrev : (1 : Fin 2).rev = 0 := by decide
  simpa only [IsIntegralLattice.realCharacter_coord, Basis.coord_apply] using
    Φ.nonneg_or_nonpos_basis_repr_on_cone b 1 σ
      (fun _ ↦ by simpa only [hrev, h₀] using (r 0).hull_primitiveGenerator_mem)
      (fun _ ↦ by simpa only [hrev, h₂] using (r 2).hull_primitiveGenerator_mem)

end TauCeti.Toric.Fan
