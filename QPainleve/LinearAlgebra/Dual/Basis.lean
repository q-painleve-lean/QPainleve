/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.Module.Primitive

import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Bases adapted to integral functionals in rank two

A surjective integral functional can serve as the second coordinate of a basis whose
first vector is a specified primitive vector in its kernel.
-/

public section

namespace Module.Basis

open TauCeti

variable {N : Type*} [AddCommGroup N]

/-- In rank two, a primitive vector in the kernel of a surjective integral functional
extends to a basis with that functional as its second coordinate. -/
theorem exists_basis_zero_eq_coord_one_eq (b₀ : Basis (Fin 2) ℤ N)
    {v : N} (hv : IsPrimitive v) {m : N →+ ℤ} (hmv : m v = 0)
    (hsurj : Function.Surjective m) :
    ∃ d : Basis (Fin 2) ℤ N, d 0 = v ∧ m = (d.coord 1).toAddMonoidHom := by
  obtain ⟨f₀, hf₀⟩ := isPrimitive_def.mp hv
  obtain ⟨c, -, hc⟩ := (b₀.exists_basis_eq_iff 0 v).mpr ⟨f₀, by simp, hf₀⟩
  obtain ⟨w, hw⟩ := hsurj 1
  have hu : IsUnit (m (c 1)) := by
    apply isUnit_of_dvd_one
    refine ⟨c.repr w 1, ?_⟩
    have he := congrArg m (c.sum_repr w)
    rw [Fin.sum_univ_two, map_add, map_zsmul, map_zsmul, hc, hmv, smul_zero, zero_add, hw,
      zsmul_eq_mul, mul_comm] at he
    exact he.symm
  let d := c.unitsSMul fun j ↦ if j = 0 then 1 else hu.unit⁻¹
  have hd : d 0 = v := by simp [d, Basis.unitsSMul_apply, hc]
  have hd₁ : m (d 1) = 1 := by
    dsimp only [d]
    rw [Basis.unitsSMul_apply, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), Units.smul_def,
      map_zsmul, zsmul_eq_mul]
    exact hu.val_inv_mul
  have he : m = (d.coord 1).toAddMonoidHom := by
    apply AddMonoidHom.toIntLinearMap_injective
    apply d.ext
    intro j
    fin_cases j
    · have h₀ : m (d 0) = 0 := by rw [hd, hmv]
      simpa [Basis.coord_apply] using h₀
    · simpa [Basis.coord_apply] using hd₁
  exact ⟨d, hd, he⟩

end Module.Basis
