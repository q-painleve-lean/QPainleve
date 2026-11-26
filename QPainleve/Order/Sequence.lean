/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Nat.Order.Lemmas
public import Mathlib.Order.Interval.Set.Defs

/-!
# Consecutive terms of a sequence
-/

public section

namespace QPainleve

/-- If a value lies weakly between the endpoints of a nonempty sequence of steps,
it lies weakly between two consecutive terms, even without monotonicity. -/
theorem exists_le_le_succ_of_le_endpoints {α : Type*} [LinearOrder α]
    {f : ℕ → α} {t : α} {n : ℕ} (hn : 0 < n) (h₀ : f 0 ≤ t) (hn' : t ≤ f n) :
    ∃ k < n, f k ≤ t ∧ t ≤ f (k + 1) := by
  by_cases h : t ≤ f 1
  · exact ⟨0, hn, h₀, h⟩
  obtain ⟨k, hk, hk'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun k ↦ t ≤ f (k + 1) ∧ k < n) (fun hk ↦ h hk.1)
    ⟨n - 1, by simpa [Nat.sub_add_cancel hn], by omega⟩
  exact ⟨k + 1, hk'.2, le_of_not_ge (fun hle ↦ hk ⟨hle, by omega⟩), hk'.1⟩

end QPainleve

/-- In a monotone sequence spanning one period, if representatives `s` and `t` of a value
`a` (each either `a` or `a + period`) lie in consecutive-term intervals at distinct indices,
then `s` is an endpoint of its interval. -/
theorem MonotoneOn.eq_endpoint_of_mem_two_periodic_intervals {α : Type*}
    [PartialOrder α] [Add α] [AddRightMono α] [AddRightReflectLE α]
    {f : ℕ → α} {n : ℕ} {period : α} (hmono : MonotoneOn f (Set.Iic n))
    (hperiod : f n = f 0 + period) {k l : ℕ} (hk : k < n) (hl : l < n) (hne : k ≠ l)
    {s t a : α} (hs : s = a ∨ s = a + period) (ht : t = a ∨ t = a + period)
    (hks : s ∈ Set.Icc (f k) (f (k + 1))) (hlt : t ∈ Set.Icc (f l) (f (l + 1))) :
    s = f k ∨ s = f (k + 1) := by
  have hle {i j : ℕ} (hj : j ≤ n) (hij : i ≤ j) : f i ≤ f j :=
    hmono (hij.trans hj) hj hij
  rcases eq_or_ne s t with rfl | hst
  · rcases lt_or_gt_of_ne hne with hkl | hlk
    · exact Or.inr (hks.2.antisymm ((hle hl.le hkl).trans hlt.1))
    · exact Or.inl ((hlt.2.trans (hle hk.le hlk)).antisymm hks.1)
  · -- Distinct representatives lie at opposite ends of the period.
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact (hst rfl).elim
    · have hupper := hlt.2.trans (hle le_rfl (Nat.succ_le_of_lt hl))
      rw [hperiod] at hupper
      have hs' := (add_le_add_iff_right period).mp hupper
      exact Or.inl ((hs'.trans (hle hk.le (Nat.zero_le k))).antisymm hks.1)
    · have hlower := (hle hl.le (Nat.zero_le l)).trans hlt.1
      have hs' := hperiod.trans_le ((add_le_add_iff_right period).mpr hlower)
      exact Or.inr (hks.2.antisymm ((hle le_rfl (Nat.succ_le_of_lt hk)).trans hs'))
    · exact (hst rfl).elim
