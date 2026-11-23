/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Numerical bounds for Sarkisov links from the quadric

For a linear system of bidegree `(a, b)` on the quadric, the homaloidal identities
give the sum of its base-point multiplicities and the sum of their squares.
Only the multiplicities greater than `b / 2` contribute positive terms to
the sum of `m * (2 * m - b)`. This yields the one- and two-point inequalities of
Lemma 8.12 in [Lutz's appendix to Hacking and Keating][HKL], with denominators cleared.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

namespace QPainleve

variable {ι : Type*} [Fintype ι] {a b : ℤ} {m : ι → ℤ}

/-- The quadric homaloidal identities bound `2 * b * a` using just a finite set
containing every multiplicity greater than `b / 2`. -/
theorem two_mul_mul_lt_of_quadric_homaloidal (hb : 0 < b) (s : Finset ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hsmall : ∀ i ∉ s, 0 ≤ m i ∧ 2 * m i ≤ b) :
    2 * b * a < 2 * b ^ 2 + ∑ i ∈ s, m i * (2 * m i - b) := by
  classical
  have hle : (∑ i, m i * (2 * m i - b)) ≤ ∑ i ∈ s, m i * (2 * m i - b) := by
    apply Finset.sum_le_sum_of_subset_of_nonpos (Finset.subset_univ s)
    intro i _ hi
    obtain ⟨hn, h⟩ := hsmall i hi
    exact mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.mpr h)
  have hcalc : (∑ i, m i * (2 * m i - b)) = 2 * (2 * a * b - 1) - b * (2 * a + 2 * b - 3) := by
    calc
      _ = ∑ i, (2 * (m i ^ 2) - b * m i) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsq, hsum]
  rw [hcalc] at hle
  have hb' : 1 ≤ b := by omega
  nlinarith only [hle, hb']

/-- The one-point quadric bound in Lutz's Lemma 8.12(1), after multiplying by
`2 * b`. All other multiplicities are at most `b / 2`. -/
theorem two_mul_mul_lt_of_quadric_homaloidal_of_single (hb : 0 < b) (j : ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hsmall : ∀ i ≠ j, 0 ≤ m i ∧ 2 * m i ≤ b) :
    2 * b * a < 2 * (b - m j) ^ 2 + 3 * b * m j := by
  have h := two_mul_mul_lt_of_quadric_homaloidal hb {j} hsq hsum (by simpa using hsmall)
  rw [Finset.sum_singleton] at h
  nlinarith only [h]

/-- The two-point quadric bound in Lutz's Lemma 8.12(2), after multiplying by
`2 * b`. All other multiplicities are at most `b / 2`. -/
theorem two_mul_mul_lt_of_quadric_homaloidal_of_pair (hb : 0 < b) {j l : ι} (hjl : j ≠ l)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hsmall : ∀ i, i ≠ j → i ≠ l → 0 ≤ m i ∧ 2 * m i ≤ b) :
    2 * b * a < 2 * ((b - m j) ^ 2 + (b - m l) ^ 2) - 2 * b ^ 2 + 3 * b * (m j + m l) := by
  classical
  have h := two_mul_mul_lt_of_quadric_homaloidal hb {j, l} hsq hsum
    (fun i hi ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact hsmall i hi.1 hi.2)
  rw [Finset.sum_pair hjl] at h
  nlinarith only [h]

end QPainleve
