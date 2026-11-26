/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Nat.Order.Lemmas

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
