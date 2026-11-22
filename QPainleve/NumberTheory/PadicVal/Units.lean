/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The prime valuation on rational units

The `p`-adic exponent is a group homomorphism on nonzero rationals. Its values on prime
units identify the prime corresponding to each coordinate of a rational product.
-/

public noncomputable section

namespace Nat.Primes

/-- A natural prime viewed as a unit in the rational field. -/
def ratUnit (p : Nat.Primes) : ℚˣ :=
  Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.prop.ne_zero)

@[simp]
theorem coe_ratUnit (p : Nat.Primes) : (p.ratUnit : ℚ) = (p : ℕ) :=
  (rfl)

/-- The `p`-adic exponent as a multiplicative homomorphism with additive integer values. -/
def ratUnitValuation (p : Nat.Primes) : ℚˣ →* Multiplicative ℤ :=
  let : Fact (p : ℕ).Prime := ⟨p.prop⟩
  (WithZero.unitsWithZeroEquiv.toMonoidHom.comp (Units.map (Rat.padicValuation p).toMonoidHom))⁻¹

@[simp]
theorem ratUnitValuation_toAdd (p : Nat.Primes) (x : ℚˣ) :
    (p.ratUnitValuation x).toAdd = padicValRat (p : ℕ) (x : ℚ) := by
  let : Fact (p : ℕ).Prime := ⟨p.prop⟩
  let u := Units.map (Rat.padicValuation p).toMonoidHom x
  have h : WithZero.unitsWithZeroEquiv u =
      Multiplicative.ofAdd (-padicValRat (p : ℕ) (x : ℚ)) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unitsWithZeroEquiv_eq_units_val]
    simp [u, Rat.padicValuation, x.ne_zero, WithZero.exp]
  -- The valuation stores the negative exponent, and the homomorphism inverts it.
  change ((WithZero.unitsWithZeroEquiv u)⁻¹).toAdd = _
  simp [h]

@[simp]
theorem ratUnitValuation_ratUnit_self (p : Nat.Primes) :
    p.ratUnitValuation p.ratUnit = Multiplicative.ofAdd 1 := by
  apply Multiplicative.toAdd.injective
  simp [padicValRat.self p.prop.one_lt]

/-- The valuation attached to a prime vanishes at every other prime unit. -/
theorem ratUnitValuation_ratUnit_of_ne {p q : Nat.Primes} (hpq : p ≠ q) :
    p.ratUnitValuation q.ratUnit = 1 := by
  apply Multiplicative.toAdd.injective
  let : Fact (p : ℕ).Prime := ⟨p.prop⟩
  let : Fact (q : ℕ).Prime := ⟨q.prop⟩
  simp [multiplicity_primes (Nat.Primes.coe_nat_injective.ne hpq)]

end Nat.Primes
