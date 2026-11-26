/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Tactic.Linarith

/-!
# Signs of sine on one full turn
-/

public section

namespace Real

/-- On the first full turn, sine is nonnegative exactly up to and including π. -/
theorem sin_nonneg_iff_of_nonneg_of_lt_two_pi {t : ℝ} (ht : 0 ≤ t)
    (ht' : t < 2 * Real.pi) : 0 ≤ Real.sin t ↔ t ≤ Real.pi := by
  refine ⟨fun hs ↦ le_of_not_gt fun h ↦ ?_, Real.sin_nonneg_of_nonneg_of_le_pi ht⟩
  have hneg : Real.sin (t - 2 * Real.pi) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  rw [Real.sin_sub_two_pi] at hneg
  exact hneg.not_ge hs

/-- On the first full turn, sine is positive exactly between zero and π. -/
theorem sin_pos_iff_of_nonneg_of_lt_two_pi {t : ℝ} (ht : 0 ≤ t)
    (ht' : t < 2 * Real.pi) : 0 < Real.sin t ↔ 0 < t ∧ t < Real.pi := by
  refine ⟨fun hs ↦ ?_, fun h ↦ sin_pos_of_pos_of_lt_pi h.1 h.2⟩
  have hp := (sin_nonneg_iff_of_nonneg_of_lt_two_pi ht ht').mp hs.le
  exact ⟨ht.lt_of_ne (by rintro rfl; simp at hs),
    hp.lt_of_ne (by rintro rfl; simp at hs)⟩

end Real
