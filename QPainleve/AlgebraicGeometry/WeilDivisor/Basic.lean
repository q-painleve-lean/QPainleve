/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic

/-!
# Coefficients of effective Weil divisors

A positive coefficient allows one copy of the corresponding prime divisor to be removed
from an effective Weil divisor.
-/

public section

namespace TauCeti.AlgebraicGeometry.WeilDivisor

/-- A point of positive coefficient contributes at least one copy of its prime divisor
to a nonnegative Weil divisor. -/
theorem single_one_le_of_coeff_pos {X : Type*} {D : WeilDivisor X} (hD : 0 ≤ D)
    {p : X} (hp : 0 < D p) : Finsupp.single p 1 ≤ D := by
  classical
  intro q
  rcases eq_or_ne q p with rfl | hq
  · rw [Finsupp.single_eq_same]
    omega
  · simpa only [Finsupp.single_eq_of_ne hq, Finsupp.zero_apply] using hD q

end TauCeti.AlgebraicGeometry.WeilDivisor
