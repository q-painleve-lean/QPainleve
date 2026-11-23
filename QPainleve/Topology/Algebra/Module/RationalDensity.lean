/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension

import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Rational points in a real scalar extension

In the real scalar extension of a module with a finite integer basis, the points
that have a positive integer multiple in the image of the integer module are dense.
This permits tests on integral classes to determine closed cones.
-/

public section

open scoped TensorProduct

namespace Module.Basis

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M] [Finite ι]

local notation "V(" N ")" => (ℝ ⊗[ℤ] N)

variable [TopologicalSpace V(M)] [IsTopologicalAddGroup V(M)] [ContinuousSMul ℝ V(M)] [T2Space V(M)]

/-- The vectors with a positive integer multiple in the integral module form a dense
set in its real scalar extension. -/
theorem dense_setOf_exists_pos_natCast_smul_eq_one_tmul (b : Basis ι ℤ M) :
    Dense {x : V(M) | ∃ n : ℕ, 0 < n ∧ ∃ a : M, (n : ℝ) • x = (1 : ℝ) ⊗ₜ[ℤ] a} := by
  let := Fintype.ofFinite ι
  let e := (b.baseChange ℝ).equivFunL
  let ratPoint (r : ι → ℚ) : V(M) := e.symm (fun j ↦ (r j : ℝ))
  have hd : DenseRange ratPoint :=
    (e.symm.surjective.denseRange).comp
      (DenseRange.piMap (fun _ ↦ Rat.denseRange_cast)) e.symm.continuous
  refine hd.mono ?_
  rintro z ⟨r, rfl⟩
  obtain ⟨d, hd⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Algebra.linearMap ℤ ℚ) r
  choose a ha using hd
  have hnum (j : ι) : ((a j : ℤ) : ℝ) = (d.val : ℝ) * r j := by
    have he : ((a j : ℤ) : ℚ) = (d.val : ℚ) * r j := by
      simpa only [Algebra.linearMap_apply, algebraMap_int_eq, Int.coe_castRingHom, zsmul_eq_mul]
        using ha j
    exact_mod_cast he
  -- Squaring the common denominator makes the multiple positive in either sign.
  let a' := b.equivFun.symm fun j ↦ d.val * a j
  let n := d.val.natAbs ^ 2
  have hn : 0 < n := pow_pos (Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero d)) _
  have hn_int : (n : ℤ) = d.val * d.val := by
    simp only [n, pow_two, Int.natAbs_mul_self]
  have hcast : (n : ℝ) = (d.val : ℝ) * (d.val : ℝ) := by exact_mod_cast hn_int
  refine ⟨n, hn, a', e.injective ?_⟩
  rw [e.map_smul, e.apply_symm_apply]
  funext j
  have ha' : b.repr a' j = d.val * a j := by
    simpa only [Module.Basis.equivFun_apply, a'] using
      congrFun (b.equivFun.apply_symm_apply (fun j ↦ d.val * a j)) j
  simp only [Pi.smul_apply, smul_eq_mul, e, Module.Basis.equivFunL_apply,
    Module.Basis.baseChange_repr_tmul, ha', ← Int.cast_smul_eq_zsmul ℝ, Int.cast_mul,
    mul_one, hnum, hcast, mul_assoc]

end Module.Basis
