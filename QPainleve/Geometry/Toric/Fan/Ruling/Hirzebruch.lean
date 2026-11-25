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

/-- The second basis character defining the Hirzebruch ruling is nonzero. -/
theorem hirzebruch_ruling_character_ne_zero : m ≠ 0 := by
  intro hz
  have ha := DFunLike.congr_fun hz (b 1)
  simp [Basis.coord_apply] at ha

include hr in
open Classical in
/-- The positive part of the chart character is one on the corresponding fiber
ray and zero on the other rays. -/
theorem hirzebruch_ruling_coordinateFiber_coefficients (k : Fin 2) :
    (fun ρ : Φ.Ray ↦ max ((if k = 0 then m else -m) ρ.primitiveGenerator) 0) =
      Pi.single (r ((![1, 3] : Fin 2 → Fin 4) k)) (1 : ℤ) := by
  funext ρ
  obtain ⟨j, rfl⟩ := r.surjective ρ
  have hj := congrFun hr j
  simp only [Equiv.apply_eq_iff_eq, Pi.single_apply]
  rw [hj]
  fin_cases k <;> fin_cases j <;> norm_num [Basis.coord_apply]

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
