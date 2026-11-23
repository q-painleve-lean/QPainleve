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

/-!
# High-multiplicity base points

The homaloidal identities force a base point of multiplicity greater than the
Sarkisov degree for a plane system of degree greater than one. On a Hirzebruch
surface they yield the same conclusion with the two exceptions for
`𝔽₀` and `𝔽₁`. The comparisons use integer multiples to avoid division.

These are the numerical estimates in Lemma 8.8 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

namespace QPainleve

variable {ι : Type*} [Fintype ι] {d : ℤ} {m : ι → ℤ} in
/-- Each base order is strictly less than the degree of a positive-degree plane system
satisfying the square homaloidal identity. -/
theorem baseOrder_lt_degree_of_plane_homaloidal (hd : 0 < d) (j : ι)
    (hsq : ∑ i, m i ^ 2 = d ^ 2 - 1) : m j < d := by
  have hbound : m j ^ 2 ≤ ∑ i, m i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (m i)) (Finset.mem_univ j)
  rw [hsq] at hbound
  by_contra! hj
  nlinarith only [hbound, mul_nonneg (sub_nonneg.mpr hj) (by omega : 0 ≤ m j + d)]

variable {ι : Type*} [Fintype ι] {m : ι → ℤ}

/-- A plane system of degree `d > 1` satisfying the homaloidal identities has
a base-point multiplicity greater than `d / 3`. -/
theorem exists_degree_lt_three_mul_of_plane_homaloidal {d : ℤ} (hd : 1 < d)
    (hm : ∀ j, 0 ≤ m j)
    (hsq : ∑ j, m j ^ 2 = d ^ 2 - 1) (hsum : ∑ j, m j = 3 * d - 3) :
    ∃ j, d < 3 * m j := by
  by_contra! h
  have hle : 3 * (∑ j, m j ^ 2) ≤ d * ∑ j, m j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ by
      have hj := mul_le_mul_of_nonneg_right (h j) (hm j)
      nlinarith only [hj]
  rw [hsq, hsum] at hle
  nlinarith only [hle, hd]

/-- For a Hirzebruch system with class `aA + bB`, where `A` is a fiber and
`B² = -e`, a bound of `b / 2` on every base-point multiplicity forces
`2a < (e + 2)b`. -/
theorem two_mul_lt_of_hirzebruch_homaloidal {e a b : ℤ} (hb : 0 < b)
    (hm : ∀ j, 0 ≤ m j ∧ 2 * m j ≤ b)
    (hsq : ∑ j, m j ^ 2 = 2 * a * b - e * b ^ 2 - 1)
    (hsum : ∑ j, m j = 2 * a + (2 - e) * b - 3) :
    2 * a < (e + 2) * b := by
  have hle : 2 * (∑ j, m j ^ 2) ≤ b * ∑ j, m j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ ↦ by
      have hj := mul_le_mul_of_nonneg_right (hm j).2 (hm j).1
      nlinarith only [hj]
  rw [hsq, hsum] at hle
  have hb₁ : 1 ≤ b := by omega
  apply lt_of_mul_lt_mul_right (a := b) ?_ hb.le
  nlinarith only [hle, hb₁]

/-- A mobile Hirzebruch system has a base-point multiplicity greater than
`b / 2`, unless it is on `𝔽₀` with `a < b` or on `𝔽₁` with
`a / 3 < b / 2`. The inequality `e * b ≤ a` is the nonnegative
intersection with the negative section. -/
theorem exists_fiber_degree_lt_two_mul_or_of_hirzebruch_homaloidal {e a b : ℤ}
    (he : 0 ≤ e) (hb : 0 < b) (ha : e * b ≤ a)
    (hm : ∀ j, 0 ≤ m j)
    (hsq : ∑ j, m j ^ 2 = 2 * a * b - e * b ^ 2 - 1)
    (hsum : ∑ j, m j = 2 * a + (2 - e) * b - 3) :
    (∃ j, b < 2 * m j) ∨ (e = 0 ∧ a < b) ∨ (e = 1 ∧ 2 * a < 3 * b) := by
  by_cases h : ∃ j, b < 2 * m j
  · exact Or.inl h
  push Not at h
  have hbound := two_mul_lt_of_hirzebruch_homaloidal hb (fun j ↦ ⟨hm j, h j⟩) hsq hsum
  have he₂ : e < 2 := by
    by_contra! he₂
    have hl := mul_le_mul_of_nonneg_right he₂ hb.le
    nlinarith only [hl, ha, hbound]
  have hcase : e = 0 ∨ e = 1 := by omega
  rcases hcase with rfl | rfl
  · exact Or.inr (Or.inl ⟨rfl, by linarith only [hbound]⟩)
  · exact Or.inr (Or.inr ⟨rfl, by norm_num at hbound; exact hbound⟩)

end QPainleve
