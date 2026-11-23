/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sarkisov degree decrease for links from the quadric

The one- and two-point blocks from the quadric strictly decrease the Sarkisov
degree. The degree after the one-point block is `(b + a - m) / 3` on the plane.
After the two-point block it is `(b + a - m₁ - m₂) / 2` on the quadric.
The homaloidal identities bound both transformed degrees below by zero and above
by the original Sarkisov degree, using the fiber-degree bound at the selected
base points. The comparisons clear denominators.

The proof uses the inequalities of Lemma 8.12 in
[Lutz's appendix to Hacking and Keating][HKL], as in Proposition 8.11.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

namespace QPainleve

variable {ι : Type*} [Fintype ι] {a b : ℤ} {m : ι → ℤ}

private theorem mul_two_mul_sub_sum_add_card_pos (s : Finset ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) :
    0 < b * (2 * (a - ∑ i ∈ s, m i) + (s.card : ℤ) * b) := by
  have hsqSubset : (∑ i ∈ s, m i ^ 2) ≤ 2 * a * b - 1 :=
    hsq ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ ↦ sq_nonneg (m i))
  -- The selected squares use only part of the homaloidal square sum.
  have hsqExpand :
      (∑ i ∈ s, (b - m i) ^ 2) =
        (s.card : ℤ) * b ^ 2 - 2 * b * (∑ i ∈ s, m i) + ∑ i ∈ s, m i ^ 2 := by
    calc
      _ = ∑ i ∈ s, (b ^ 2 - 2 * b * m i + m i ^ 2) :=
        Finset.sum_congr rfl fun i _ ↦ by ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
  have hnonneg := Finset.sum_nonneg (s := s) fun i _ ↦ sq_nonneg (b - m i)
  rw [hsqExpand] at hnonneg
  nlinarith only [hsqSubset, hnonneg]

/-- The homaloidal identities bound the adjusted coefficient
`2(a - ∑ mᵢ) + |s|b` strictly between zero and `2b`. The selected
multiplicities are between half the fiber degree and the full fiber degree. The
remaining multiplicities are nonnegative and at most half the fiber degree. -/
theorem quadric_sarkisov_degree_bounds (hb : 0 < b) (s : Finset ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hlarge : ∀ i ∈ s, b ≤ 2 * m i ∧ m i ≤ b)
    (hsmall : ∀ i ∉ s, 0 ≤ m i ∧ 2 * m i ≤ b) :
    0 < 2 * (a - ∑ i ∈ s, m i) + (s.card : ℤ) * b ∧
      2 * (a - ∑ i ∈ s, m i) + (s.card : ℤ) * b < 2 * b := by
  refine ⟨pos_of_mul_pos_right (mul_two_mul_sub_sum_add_card_pos s hsq) hb.le, ?_⟩
  have hbound := two_mul_mul_lt_of_quadric_homaloidal hb s hsq hsum hsmall
  have hterms :
      (∑ i ∈ s, m i * (2 * m i - b)) ≤ ∑ i ∈ s, b * (2 * m i - b) := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    exact mul_le_mul_of_nonneg_right (hlarge i hi).2 (sub_nonneg.mpr (hlarge i hi).1)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at hterms
  apply lt_of_mul_lt_mul_left (a := b) ?_ hb.le
  nlinarith only [hbound, hterms]

/-- In the one-point block the new plane degree `b + a - m j` is positive, and its
Sarkisov degree is strictly smaller than the original fiber degree divided by two. -/
theorem quadric_sarkisov_degree_decrease_of_single (hb : 0 < b) (j : ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hj : b ≤ 2 * m j) (hj' : m j ≤ b)
    (hsmall : ∀ i ≠ j, 0 ≤ m i ∧ 2 * m i ≤ b) :
    0 < b + a - m j ∧ 2 * (b + a - m j) < 3 * b := by
  have h := quadric_sarkisov_degree_bounds hb {j} hsq hsum
    (by simpa using ⟨hj, hj'⟩) (by simpa using hsmall)
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one] at h
  omega

/-- In the two-point block the new quadric fiber degree is positive and strictly
smaller than the original one. In particular the selected multiplicities have
sum greater than the other ruling coefficient. -/
theorem quadric_sarkisov_degree_decrease_of_pair (hb : 0 < b) {j l : ι} (hjl : j ≠ l)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - 1) (hsum : ∑ i, m i = 2 * a + 2 * b - 3)
    (hj : b ≤ 2 * m j) (hj' : m j ≤ b) (hl : b ≤ 2 * m l) (hl' : m l ≤ b)
    (hsmall : ∀ i, i ≠ j → i ≠ l → 0 ≤ m i ∧ 2 * m i ≤ b) :
    0 < b + a - m j - m l ∧ b + a - m j - m l < b := by
  classical
  have h := quadric_sarkisov_degree_bounds hb {j, l} hsq hsum
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨hj, hj'⟩
      · exact ⟨hl, hl'⟩)
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      exact hsmall i hi.1 hi.2)
  have hcard : ({j, l} : Finset ι).card = 2 :=
    Finset.card_pair hjl
  rw [Finset.sum_pair hjl, hcard] at h
  omega

end QPainleve
