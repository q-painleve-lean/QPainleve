/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic

/-!
# Primitivity from a characteristic vector

An isotropic vector pairing to minus two with a characteristic vector is primitive.
This applies to the fiber class on a rational ruled surface by adjunction.
-/

public section

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
  {B : LinearMap.BilinForm ℤ M} {K F : M}

/-- An isotropic vector of characteristic degree minus two is primitive. -/
theorem IsCharacteristic.isPrimitive_of_apply_eq_neg_two (hK : B.IsCharacteristic K)
    (hFF : B F F = 0) (hKF : B K F = -2) : TauCeti.IsPrimitive F := by
  obtain ⟨d, G, hd, hG, hFG⟩ := TauCeti.exists_eq_zsmul_isPrimitive
    (v := F) (fun h ↦ by simp [h] at hKF)
  have hG₂ : B G G = 0 := by
    simpa only [hFG, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id,
      mul_eq_zero, hd.ne', false_or] using hFF
  obtain ⟨a, ha⟩ := isCharacteristic_iff.mp hK G
  rw [hG₂, sub_zero] at ha
  have hmul : d * B K G = -2 := by
    simpa only [hFG, map_zsmul, zsmul_eq_mul, Int.cast_id] using hKF
  have hd₁ : d * a = -1 := by
    rw [ha, mul_left_comm] at hmul
    omega
  have hd' : d = 1 := by
    rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hd₁ with h | h
    · exact h.1
    · omega
  rwa [hFG, hd', one_smul]

end LinearMap.BilinForm
