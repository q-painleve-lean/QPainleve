/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Integer powers and additive valuations

For valuations valued in `WithTop Γ`, an integer power of an element with
finite value scales that value in the underlying ordered group `Γ`.
-/

public section

namespace AddValuation

variable {K Γ : Type*} [DivisionRing K] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- If an element has finite value, its integer power has value given by the
corresponding integer multiple. -/
theorem map_zpow_of_eq_coe (v : AddValuation K (WithTop Γ)) {x : K} {g : Γ}
    (h : v x = g) (n : ℤ) : v (x ^ n) = (n • g : Γ) := by
  cases n with
  | ofNat n => simp [v.map_pow, h]
  | negSucc n => simp [zpow_negSucc, v.map_pow, h, negSucc_zsmul]

end AddValuation
