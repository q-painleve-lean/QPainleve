/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.Matrix.Kernel.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Group.Int.Units
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Sign-normalized generators of integral matrix kernels

When the integral kernel has rank one, its computed basis vector can be oriented
by the sign of a chosen coordinate. For a kernel spanned by a strictly positive
vector, every coordinate gives the same orientation.
-/

public section

namespace Matrix

open Module

/-- Return the computed integral basis vector of a rank-one kernel, oriented so
that its coordinate at `i` is nonnegative. Return `none` at other ranks. -/
def intKernelGenerator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin n) :
    Option (Fin n → ℤ) :=
  let b := A.intKernelBasisVectors
  if h : b.1 = 1 then
    let x := b.2 ⟨0, by omega⟩
    some (if x i < 0 then -x else x)
  else none

/-- If the integral kernel is spanned by `x` and `x` has positive coordinate at
`i`, the sign-normalized computation returns `x`. -/
theorem intKernelGenerator_eq_some_of_span {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    {x : Fin n → ℤ} {i : Fin n} (hi : 0 < x i)
    (hker : A.mulVecLin.ker = Submodule.span ℤ {x}) :
    A.intKernelGenerator i = some x := by
  obtain ⟨b, hb⟩ := A.exists_basis_eq_intKernelBasisVectors
  let f := LinearMap.toSpanSingleton ℤ (Fin n → ℤ) x
  have hf : Function.Injective f := by
    intro a b hab
    exact mul_right_cancel₀ hi.ne' (congrFun hab i)
  have hdim : finrank ℤ A.mulVecLin.ker = 1 := by
    rw [hker, LinearMap.span_singleton_eq_range]
    exact (LinearEquiv.ofInjective f hf).finrank_eq.symm.trans (finrank_self ℤ)
  have hr : A.intKernelBasisVectors.1 = 1 := by
    simpa only [finrank_eq_card_basis b, Fintype.card_fin] using hdim
  let j : Fin A.intKernelBasisVectors.1 := ⟨0, by omega⟩
  have hx : x ∈ A.mulVecLin.ker := hker ▸ Submodule.mem_span_singleton_self x
  have hj : (b j : Fin n → ℤ) ∈ Submodule.span ℤ {x} := hker ▸ (b j).property
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hj
  let y : A.mulVecLin.ker := ⟨x, hx⟩
  have hay : a • y = b j := Subtype.ext ha
  -- A basis coordinate takes the chosen vector to one, so the multiplier is a unit.
  have hab := congrArg (b.coord j) hay
  simp only [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul] at hab
  rw [intKernelGenerator, dite_eq_left hr, ← hb]
  rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hab) with rfl | rfl
  · have h : (b j : Fin n → ℤ) = x := by simpa using ha.symm
    simp [j] at h
    simp [h, hi.not_gt]
  · have h : (b j : Fin n → ℤ) = -x := by simpa using ha.symm
    simp [j] at h
    simp [h, hi]

end Matrix
