/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Positive pivot counts in Hirzebruch-to-plane resolutions

When the high orders lie off the strict positive section, the section order
sum and the square homaloidal identity force enough positive section orders
to choose one for each step of the greedy preparation.
-/

public section

namespace QPainleve

/-- If the strict positive section has residual line degree at most one and
none of its orders exceeds half the fiber degree, the presence of a high
order forces at least `2 * e - 1` positive orders on the section of a
Hirzebruch surface of index `e`, enough to choose `e` positive orders. -/
theorem two_mul_index_le_card_positiveSection_add_one {ι : Type*} [Fintype ι]
    (s : Finset ι) (m : ι → ℤ) (e : ℕ) {a b : ℤ}
    (hb : 0 < b) (ha : (e : ℤ) * b ≤ a)
    (hm : ∀ j ∈ s, 0 ≤ m j) (hlow : ∀ j ∈ s, 2 * m j ≤ b)
    (hhigh : ∃ j, b < 2 * m j) (hline : a - 1 ≤ ∑ j ∈ s, m j)
    (hsq : ∑ j, m j ^ 2 = 2 * a * b - (e : ℤ) * b ^ 2 - 1) :
    2 * e ≤ (s.filter fun j ↦ 0 < m j).card + 1 := by
  classical
  by_cases he : e = 0
  · simp [he]
  -- Fiber degree one would force the square sum to vanish despite a high order.
  have hb₂ : 2 ≤ b := by
    by_contra! hb₂
    have hb₁ : b = 1 := by omega
    subst b
    have hz (j) (hj : j ∈ s) : m j = 0 := by
      have := hm j hj
      have := hlow j hj
      omega
    rw [Finset.sum_eq_zero hz] at hline
    obtain ⟨j, hj⟩ := hhigh
    have hpos : 0 < m j := by omega
    have hsqpos : 0 < ∑ l, m l ^ 2 :=
      (sq_pos_of_pos hpos).trans_le
        (Finset.single_le_sum (fun l _ ↦ sq_nonneg (m l)) (Finset.mem_univ j))
    simp only [mul_one, one_pow] at ha hsq
    omega
  let positive := s.filter (fun j ↦ 0 < m j)
  have hsum : (∑ j ∈ positive, m j) = ∑ j ∈ s, m j := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j hj ↦ by
      by_cases h : 0 < m j
      · simp [h]
      · simp [le_antisymm (le_of_not_gt h) (hm j hj)]
  have hbound : 2 * (∑ j ∈ positive, m j) ≤ (positive.card : ℤ) * b := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun j hj ↦ hlow j (Finset.mem_filter.mp hj).1 :
        ∑ j ∈ positive, 2 * m j ≤ ∑ _j ∈ positive, b)
  rw [hsum] at hbound
  by_contra! hcard
  have hcard' : positive.card + 1 < 2 * e := hcard
  have hgap : (positive.card : ℤ) + 2 ≤ 2 * e := by
    exact_mod_cast (by omega : positive.card + 2 ≤ 2 * e)
  -- Every positive section order contributes at most half the fiber degree.
  nlinarith only [hbound, ha, hline, hb₂, mul_nonneg hb.le (sub_nonneg.mpr hgap)]

end QPainleve
