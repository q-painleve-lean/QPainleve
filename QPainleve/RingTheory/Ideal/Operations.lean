/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Powers of sums of ideals

A power of a sum of ideals can be split according to which summand supplies a prescribed
number of factors. This tracks the residual degree in each summand, as needed when splitting
homogeneous numerators in a Rees algebra. The binomial expansion also used in Mathlib's
`Ideal.sup_pow_add_le_pow_sup_pow` keeps track of this degree.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- In a product of `m + n` factors from `I ⊔ J`, one can take `m` factors from `I`
or `n` factors from `J`, leaving the other factors in `I ⊔ J`. -/
theorem sup_pow_add_eq_pow_mul_sup_pow_mul (I J : Ideal R) (m n : ℕ) :
    (I ⊔ J) ^ (m + n) = I ^ m * (I ⊔ J) ^ n ⊔ J ^ n * (I ⊔ J) ^ m := by
  have split (P Q : Ideal R) {i j a b : ℕ} (hi : a ≤ i) (hij : i + j = a + b) :
      P ^ i * Q ^ j ≤ P ^ a * (P ⊔ Q) ^ b := by
    have he : i - a + j = b := by omega
    calc
      _ = P ^ a * (P ^ (i - a) * Q ^ j) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
      _ ≤ _ := Ideal.mul_mono le_rfl (by
        simpa only [← pow_add, he] using
          Ideal.mul_mono (Ideal.pow_right_mono (le_sup_left : P ≤ P ⊔ Q) (i - a))
            (Ideal.pow_right_mono (le_sup_right : Q ≤ P ⊔ Q) j))
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
    refine Finset.sup_le fun i hi ↦ Ideal.mul_le_left.trans ?_
    rw [Ideal.add_eq_sup]
    have hi' : i ≤ m + n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hm : m ≤ i
    · exact (split I J hm (by omega)).trans le_sup_left
    · rw [mul_comm (I ^ i)]
      exact (split J I (a := n) (b := m) (by omega) (by omega)).trans
        (by rw [sup_comm J I]; exact le_sup_right)
  · rw [pow_add]
    exact Ideal.mul_mono (Ideal.pow_right_mono le_sup_left m) le_rfl
  · rw [Nat.add_comm, pow_add]
    exact Ideal.mul_mono (Ideal.pow_right_mono le_sup_right n) le_rfl

end Ideal
