/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Solutions of power equations on units

A nonzero integer power of a unit gives a polynomial equation in the unit's
value, after inverting the target when the exponent is negative.
-/

public section

open Polynomial in
/-- Over an integral domain, an equation prescribing a nonzero integer power of a unit has
finitely many solutions. -/
theorem Units.finite_setOf_zpow_eq {R : Type*} [CommRing R] [IsDomain R]
    {n : ℤ} (hn : n ≠ 0) (v : Rˣ) :
    {u : Rˣ | u ^ n = v}.Finite := by
  let w := if 0 ≤ n then v else v⁻¹
  have hp := X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)) (w : R)
  refine ((finite_setOfPred_isRoot hp).preimage Units.val_injective.injOn).subset ?_
  intro u hu
  have h : u ^ n.natAbs = w := by
    change u ^ n = v at hu
    cases n with
    | ofNat m => simpa [w] using hu
    | negSucc m => simpa [w, zpow_negSucc] using congrArg Inv.inv hu
  simpa [IsRoot, sub_eq_zero] using congrArg (fun z : Rˣ ↦ (z : R)) h
