/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Piecewise-linear transvections

A linear functional vanishing on the direction of a transvection is preserved by that
transvection. This permits gluing the transvection on the nonnegative half-space to the
identity on the nonpositive half-space, with an inverse obtained by reversing the direction.

This is the positive-part form of the tropical transformations in Gross, Hacking and
Keel, *Birational geometry of cluster algebras*, (1.4) and §3.
-/

public section

namespace LinearMap

variable {R V : Type*} [CommRing R] [LinearOrder R] [AddCommGroup V] [Module R V]

/-- The shear `x ↦ x + max (f x) 0 • v`, with inverse given by shearing along `-v`. -/
def piecewiseTransvection (f : Module.Dual R V) (v : V) (h : f v = 0) : V ≃ V where
  toFun x := x + max (f x) 0 • v
  invFun x := x - max (f x) 0 • v
  left_inv x := by simp [h]
  right_inv x := by simp [h]

/-- The value of the piecewise transvection at a vector. -/
theorem piecewiseTransvection_apply (f : Module.Dual R V) (v : V) (h : f v = 0) (x : V) :
    f.piecewiseTransvection v h x = x + max (f x) 0 • v :=
  (rfl)

@[simp]
theorem piecewiseTransvection_symm (f : Module.Dual R V) (v : V) (h : f v = 0) :
    (f.piecewiseTransvection v h).symm = f.piecewiseTransvection (-v) (by simp [h]) := by
  ext x
  simp [piecewiseTransvection, sub_eq_add_neg]

/-- The shear preserves the functional defining its two half-spaces. -/
@[simp]
theorem apply_piecewiseTransvection (f : Module.Dual R V) (v : V) (h : f v = 0) (x : V) :
    f (f.piecewiseTransvection v h x) = f x := by
  simp [piecewiseTransvection_apply, h]

/-- On the nonpositive half-space the shear fixes every vector. -/
theorem piecewiseTransvection_apply_of_nonpos {f : Module.Dual R V} {v x : V}
    {h : f v = 0} (hx : f x ≤ 0) :
    f.piecewiseTransvection v h x = x := by
  simp [piecewiseTransvection_apply, max_eq_right hx]

/-- On the nonnegative half-space the shear agrees with the linear transvection. -/
theorem piecewiseTransvection_apply_of_nonneg {f : Module.Dual R V} {v x : V}
    {h : f v = 0} (hx : 0 ≤ f x) :
    f.piecewiseTransvection v h x = LinearEquiv.transvection h x := by
  simp [piecewiseTransvection_apply, LinearMap.transvection.apply, max_eq_left hx]

/-- The piecewise transvection commutes with nonnegative scaling. -/
theorem piecewiseTransvection_smul [PosMulMono R]
    (f : Module.Dual R V) (v : V) (h : f v = 0) {a : R} (ha : 0 ≤ a) (x : V) :
    f.piecewiseTransvection v h (a • x) = a • f.piecewiseTransvection v h x := by
  simp only [piecewiseTransvection_apply, map_smul, smul_eq_mul, smul_add, smul_smul]
  rw [mul_max_of_nonneg _ _ ha, mul_zero]

end LinearMap
