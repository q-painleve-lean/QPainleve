/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Rational units from primes

A natural prime determines a unit of the rational field.
-/

public noncomputable section

namespace Nat.Primes

/-- A natural prime viewed as a unit in the rational field. -/
def ratUnit (p : Nat.Primes) : ℚˣ :=
  Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.prop.ne_zero)

@[simp]
theorem coe_ratUnit (p : Nat.Primes) : (p.ratUnit : ℚ) = (p : ℕ) :=
  (rfl)

end Nat.Primes
