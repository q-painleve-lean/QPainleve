/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive-section multiplicities in Sarkisov descent

For a plane linear system resolved from a Hirzebruch surface, let `a` and `b` be the
fiber and negative-section coefficients of its base class. If the strict positive
section has residual line degree at most one, the orders on that section have
sum at least `a - 1`. Taking the largest such orders, with ties broken by the
original tower order, produces the numerical bound for the subsequent plane
or quadric link.

The homaloidal identities use the convention of Lutz's appendix to Hacking and
Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*,
Proposition 8.11](https://arxiv.org/abs/2005.05010v3). The estimate below uses the
residual degree of the positive section as an additional input.
-/

public section

namespace QPainleve

variable {ι : Type*}

private theorem exists_ordered_section_prefix [LinearOrder ι]
    (s : Finset ι) (m : ι → ℤ) (k : ℕ) :
    ∃ top ⊆ s, top.card = min k s.card ∧
      (∀ i ∈ top, ∀ j ∈ s, j < i → m i ≤ m j → j ∈ top) ∧
      ∀ i ∈ top, ∀ j ∈ s, j ∉ top → m j ≤ m i := by
  let key (j : ι) := toLex (-m j, j)
  let r (i j : ι) := key i ≤ key j
  let : DecidableRel r := fun i j ↦ inferInstanceAs (Decidable (key i ≤ key j))
  let : IsTrans ι r := ⟨fun _ _ _ ↦ le_trans⟩
  let : Std.Total r := ⟨fun i j ↦ le_total (key i) (key j)⟩
  let : Std.Antisymm r := ⟨fun _ _ hij hji ↦
    congrArg (fun x ↦ (ofLex x).2) (le_antisymm hij hji)⟩
  let ordered := s.sort r
  let top := (ordered.take k).toFinset
  have hordered : ordered.Pairwise r := s.pairwise_sort r
  have hsub : top ⊆ s := fun j hj ↦
    (Finset.mem_sort r).mp (List.mem_of_mem_take (List.mem_toFinset.mp hj))
  have hcard : top.card = min k s.card := by
    rw [List.toFinset_card_of_nodup ((s.sort_nodup r).sublist (List.take_sublist k ordered)),
      List.length_take, Finset.length_sort]
  have horder (i) (hi : i ∈ top) (j) (hj : j ∈ s) (hj' : j ∉ top) :
      -m i ≤ -m j ∧ (-m i = -m j → i ≤ j) := by
    have hmem : j ∈ ordered.take k ++ ordered.drop k := by
      rw [List.take_append_drop]
      exact (Finset.mem_sort r).mpr hj
    have htail := (List.mem_append.mp hmem).resolve_left (fun h ↦ hj' (List.mem_toFinset.mpr h))
    exact Prod.Lex.toLex_le_toLex'.mp
      (hordered.rel_of_mem_take_of_mem_drop (List.mem_toFinset.mp hi) htail)
  refine ⟨top, hsub, hcard, ?_, fun i hi j hj hj' ↦ neg_le_neg_iff.mp (horder i hi j hj hj').1⟩
  intro i hi j hj hji hweight
  by_contra hj'
  obtain ⟨h₁, h₂⟩ := horder i hi j hj hj'
  exact hji.not_ge (h₂ (by omega))

private theorem exists_largest_section_orders [LinearOrder ι]
    (s : Finset ι) (m : ι → ℤ) (k : ℕ) {b : ℤ} (hb : 0 ≤ b)
    (hm : ∀ j ∈ s, 0 ≤ m j ∧ 2 * m j ≤ b) :
    ∃ (top : Finset ι) (t : ℤ), top ⊆ s ∧ top.card = min k s.card ∧
      (∀ i ∈ top, ∀ j ∈ s, j < i → m i ≤ m j → j ∈ top) ∧
      0 ≤ t ∧ 2 * t ≤ b ∧ (top.card : ℤ) * t = (k : ℤ) * t ∧
      (∀ j ∈ top, t ≤ m j) ∧ (∀ j ∈ s, j ∉ top → m j ≤ t) := by
  classical
  obtain ⟨top, hsub, hcard, hclosed, horder⟩ := exists_ordered_section_prefix s m k
  -- The largest unused order is the cutoff. Zero also covers an empty remainder.
  let rest := insert 0 ((s \ top).image m)
  let hn : rest.Nonempty := ⟨0, Finset.mem_insert_self ..⟩
  let t := rest.max' hn
  have hmem : t ∈ rest := rest.max'_mem hn
  have hrest (j) (hj : j ∈ s) (hj' : j ∉ top) : m j ≤ t :=
    rest.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem m
      (Finset.mem_sdiff.mpr ⟨hj, hj'⟩)))
  have ht : 0 ≤ t := rest.le_max' _ (Finset.mem_insert_self ..)
  refine ⟨top, t, hsub, hcard, hclosed, ht, ?_, ?_, ?_, hrest⟩
  · rcases Finset.mem_insert.mp hmem with ht | ht
    · omega
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ht
      exact he ▸ (hm j (Finset.mem_sdiff.mp hj).1).2
  · rcases le_total k s.card with hk | hk
    · rw [hcard, min_eq_left hk]
    · have he := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, min_eq_right hk])
      have ht : t = 0 := by simp [t, rest, he]
      simp [ht]
  · intro j hj
    rcases Finset.mem_insert.mp hmem with ht | ht
    · rw [ht]
      exact (hm j (hsub hj)).1
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ht
      obtain ⟨his, hit⟩ := Finset.mem_sdiff.mp hi
      exact he ▸ horder j hj i his hit

private theorem section_deficit_le
    (s top : Finset ι) (m : ι → ℤ) {a b k t : ℤ} (hsub : top ⊆ s) (ht : 2 * t ≤ b)
    (hpad : (top.card : ℤ) * t = k * t) (hnef : k * b ≤ a)
    (hline : a - 1 ≤ ∑ j ∈ s, m j) (hm : ∀ j ∈ s, 0 ≤ m j ∧ m j ≤ b)
    (htop : ∀ j ∈ top, t ≤ m j) (hrest : ∀ j ∈ s, j ∉ top → m j ≤ t) :
    b * (k * b - 2 * (∑ j ∈ top, m j)) - (b - 2 * t) ≤ ∑ j ∈ s, m j * (b - 2 * m j) := by
  classical
  have bound (j) (hj : j ∈ s) :
      (b - 2 * t) * m j - (if j ∈ top then 2 * b * (m j - t) else 0) ≤ m j * (b - 2 * m j) := by
    by_cases hj' : j ∈ top
    · simp only [ite_eq_left hj']
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hm j hj).2) (sub_nonneg.mpr (htop j hj'))]
    · simp only [ite_eq_right hj', sub_zero]
      nlinarith only [mul_nonneg (hm j hj).1 (sub_nonneg.mpr (hrest j hj hj'))]
  have total := Finset.sum_le_sum bound
  have hfilter : s.filter (· ∈ top) = top := Finset.filter_mem_eq_inter.trans
    (Finset.inter_eq_right.mpr hsub)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter, hfilter,
    ← Finset.mul_sum, Finset.sum_sub_distrib] at total
  simp only [Finset.sum_const, nsmul_eq_mul, hpad] at total
  have hsection : 0 ≤ (∑ j ∈ s, m j) - (k * b - 1) := by linarith only [hnef, hline]
  nlinarith only [total, mul_nonneg (sub_nonneg.mpr ht) hsection]

private theorem twice_sum_sq_le_of_section_orders [Fintype ι]
    (s high : Finset ι) (m : ι → ℤ) (b : ℤ)
    (hpos : ∀ j, 0 ≤ m j) (hhigh : ∀ j ∈ high, b < 2 * m j ∧ m j ≤ b)
    (hlow : ∀ j ∉ high, 2 * m j ≤ b) (hdisj : Disjoint s high) :
    2 * (∑ j, m j ^ 2) ≤ b * (∑ j, m j) + 2 * b * (∑ j ∈ high, m j)
      - (high.card : ℤ) * b ^ 2 - ∑ j ∈ s, m j * (b - 2 * m j) := by
  classical
  have point (j : ι) : 2 * m j ^ 2 ≤ b * m j +
      (if j ∈ high then 2 * b * m j - b ^ 2 else 0) -
      (if j ∈ s then m j * (b - 2 * m j) else 0) := by
    by_cases hh : j ∈ high
    · have hjs : j ∉ s := fun hj ↦ Finset.disjoint_left.mp hdisj hj hh
      simp only [ite_eq_left hh, ite_eq_right hjs, sub_zero]
      obtain ⟨h₁, h₂⟩ := hhigh j hh
      nlinarith only [mul_nonneg (sub_nonneg.mpr h₁.le) (sub_nonneg.mpr h₂)]
    · by_cases hj : j ∈ s
      · simp only [ite_eq_right hh, ite_eq_left hj, add_zero]
        nlinarith only
      · simp only [ite_eq_right hh, ite_eq_right hj, sub_zero, add_zero]
        nlinarith only [mul_nonneg (hpos j) (sub_nonneg.mpr (hlow j hh))]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ point j)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at total
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at total
  linarith only [total]

/-- A Hirzebruch homaloidal system with every high order bounded by the fiber degree
has index at most one more than the number of high orders. -/
theorem hirzebruch_index_le_card_high_add_one [Fintype ι]
    (high : Finset ι) (m : ι → ℤ) (k : ℕ) {a b : ℤ}
    (hb : 0 < b) (hnef : (k : ℤ) * b ≤ a) (hm : ∀ j, 0 ≤ m j)
    (hhigh : ∀ j ∈ high, b < 2 * m j ∧ m j ≤ b)
    (hlow : ∀ j ∉ high, 2 * m j ≤ b)
    (hsq : ∑ j, m j ^ 2 = 2 * a * b - (k : ℤ) * b ^ 2 - 1)
    (hsum : ∑ j, m j = 2 * a + (2 - (k : ℤ)) * b - 3) :
    k ≤ high.card + 1 := by
  have h := twice_sum_sq_le_of_section_orders ∅ high m b hm hhigh hlow (by simp)
  rw [Finset.sum_empty, sub_zero, hsq, hsum] at h
  have hsumHigh : ∑ j ∈ high, m j ≤ (high.card : ℤ) * b := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun j hj ↦ (hhigh j hj).2 : ∑ j ∈ high, m j ≤ ∑ _j ∈ high, b)
  by_contra! hk
  have hcard : (high.card : ℤ) + 2 ≤ k := by exact_mod_cast hk
  nlinarith only [h, (by omega : 1 ≤ b),
    mul_nonneg hb.le (sub_nonneg.mpr hsumHigh),
    mul_nonneg hb.le (sub_nonneg.mpr hnef),
    mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hcard)]

private theorem preparation_degree_drop_of_fiberDegree_eq_one (s high top : Finset ι)
    (m : ι → ℤ) {a : ℤ} (hsub : top ⊆ s) (hpos : ∀ j, 0 ≤ m j)
    (hhigh : ∀ j ∈ high, 1 < 2 * m j ∧ m j ≤ 1) (hsmall : ∀ j ∈ s, 2 * m j ≤ 1)
    (hnonempty : high.Nonempty) (hline : a - 1 ≤ ∑ j ∈ s, m j) :
    2 * (a - (∑ j ∈ top, m j) - (∑ j ∈ high, m j)) < 2 - (high.card : ℤ) := by
  have hz (j) (hj : j ∈ s) : m j = 0 := by
    have := hsmall j hj
    have := hpos j
    omega
  have h1 (j) (hj : j ∈ high) : m j = 1 := by
    have := hhigh j hj
    omega
  rw [Finset.sum_eq_zero hz] at hline
  rw [Finset.sum_eq_zero (fun j hj ↦ hz j (hsub hj)), Finset.sum_congr rfl h1]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have := Finset.card_pos.mpr hnonempty
  omega

/-- Choose up to `k` largest orders on a positive section of a Hirzebruch surface
of index `k`. Earlier indices with equal order take priority. The section's
residual line degree is at most one, expressed by the lower bound on its order
sum. The resulting bound on the prepared degree holds for every choice of
transported high orders that are at least their original values. -/
theorem exists_preparation_with_degree_drop [Fintype ι] [LinearOrder ι]
    (s high : Finset ι) (m : ι → ℤ) (k : ℕ) {a b : ℤ}
    (hb : 0 < b) (hnef : (k : ℤ) * b ≤ a)
    (hpos : ∀ j, 0 ≤ m j) (hhigh : ∀ j ∈ high, b < 2 * m j ∧ m j ≤ b)
    (hlow : ∀ j ∉ high, 2 * m j ≤ b) (hdisj : Disjoint s high)
    (hnonempty : high.Nonempty) (hline : a - 1 ≤ ∑ j ∈ s, m j)
    (hsq : ∑ j, m j ^ 2 = 2 * a * b - (k : ℤ) * b ^ 2 - 1)
    (hsum : ∑ j, m j = 2 * a + (2 - (k : ℤ)) * b - 3) :
    ∃ top ⊆ s, top.card = min k s.card ∧
      (∀ i ∈ top, ∀ j ∈ s, j < i → m i ≤ m j → j ∈ top) ∧
      (∀ i ∈ top, ∀ j ∈ s, j ∉ top → m j ≤ m i) ∧
      ∀ μ : ι → ℤ, (∀ j ∈ high, m j ≤ μ j) →
        2 * (a - (∑ j ∈ top, m j) - (∑ j ∈ high, μ j)) < (2 - (high.card : ℤ)) * b := by
  have hslo (j) (hj : j ∈ s) := hlow j (Finset.disjoint_left.mp hdisj hj)
  obtain ⟨top, t, hsub, hcard, hclosed, ht, htb, hpad, htop, hrest⟩ :=
    exists_largest_section_orders s m k hb.le (fun j hj ↦ ⟨hpos j, hslo j hj⟩)
  refine ⟨top, hsub, hcard, hclosed, fun i hi j hj h ↦ (hrest j hj h).trans (htop i hi), ?_⟩
  have hdrop : 2 * (a - (∑ j ∈ top, m j) - (∑ j ∈ high, m j)) < (2 - (high.card : ℤ)) * b := by
    by_cases hone : b = 1
    · subst b
      simpa only [mul_one] using
        preparation_degree_drop_of_fiberDegree_eq_one s high top m
          hsub hpos hhigh hslo hnonempty hline
    have hdef := section_deficit_le s top m hsub htb hpad hnef hline
      (fun j hj ↦ ⟨hpos j, by have := hslo j hj; omega⟩) htop hrest
    have total := twice_sum_sq_le_of_section_orders s high m b hpos hhigh hlow hdisj
    -- The two homaloidal identities turn the square-sum bound into the degree comparison.
    rw [hsq, hsum] at total
    by_contra! h
    nlinarith only [total, hdef, ht, (by omega : 2 ≤ b), mul_nonneg hb.le (sub_nonneg.mpr h)]
  intro μ hμ
  have hle := Finset.sum_le_sum hμ
  omega

end QPainleve
