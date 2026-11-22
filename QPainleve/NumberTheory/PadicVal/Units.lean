/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.NumberTheory.Prime.Units
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Prime valuations of rational-unit characters

Valuation at each assigned prime recovers the corresponding exponent of a character
determined by distinct rational prime units.
-/

public section

namespace QPainleve

open TauCeti

/-- For distinct assigned primes, the valuation at the prime assigned to an index recovers
the exponent at that index. -/
theorem padicValRat_freeAbelianCharEquiv_symm {ι : Type*} (p : ι ↪ Nat.Primes)
    (i : ι) (x : ι →₀ ℤ) :
    padicValRat (p i) (↑(freeAbelianCharEquiv.symm (fun j ↦ (p j).ratUnit)
      (Multiplicative.ofAdd x)) : ℚ) = x i := by
  classical
  let : Fact (p i : ℕ).Prime := ⟨(p i).prop⟩
  let u := freeAbelianCharEquiv.symm (fun j ↦ (p j).ratUnit) (Multiplicative.ofAdd x)
  let v := Rat.padicValuation (p i)
  have h : v (u : ℚ) = WithZero.exp (-x i) := calc
    _ = (v.toMonoidHom.comp (Units.coeHom ℚ)) u := rfl
    _ = x.prod (fun j n ↦ v (↑((p j).ratUnit ^ n : ℚˣ))) := by
      dsimp only [u]
      rw [freeAbelianCharEquiv_symm_apply_ofAdd, map_finsuppProd]
      rfl
    _ = _ := by
      rw [Finsupp.prod_eq_single i]
      · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Nat.Primes.coe_ratUnit]
        dsimp only [v]
        rw [Rat.padicValuation_self, ← WithZero.exp_zsmul]
        simp
      · intro j _ hji
        have hj : v ((p j).ratUnit : ℚ) = 1 := by
          dsimp only [v]
          rw [Nat.Primes.coe_ratUnit, Rat.padicValuation_natCast, Int.padicValuation_eq_one_iff,
            Int.natCast_dvd_natCast, (p j).prop.dvd_iff_eq (p i).prop.ne_one]
          exact Nat.Primes.coe_nat_injective.ne (p.injective.ne hji)
        rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hj, one_zpow]
      · simp
  change (if (u : ℚ) = 0 then 0 else WithZero.exp (-padicValRat (p i) u)) = _ at h
  rw [ite_eq_right u.ne_zero] at h
  exact neg_injective (WithZero.exp_injective h)

/-- The character determined by distinct rational prime units is injective. -/
theorem freeAbelianCharEquiv_symm_ratUnit_injective {ι : Type*} (p : ι ↪ Nat.Primes) :
    Function.Injective (freeAbelianCharEquiv.symm fun i ↦ (p i).ratUnit) := by
  intro x y h
  rw [← ofAdd_toAdd x, ← ofAdd_toAdd y] at h
  apply Multiplicative.toAdd.injective
  exact Finsupp.ext fun i ↦ by
    simpa only [padicValRat_freeAbelianCharEquiv_symm] using
      congrArg (fun z : ℚˣ ↦ padicValRat (p i) (z : ℚ)) h

end QPainleve
