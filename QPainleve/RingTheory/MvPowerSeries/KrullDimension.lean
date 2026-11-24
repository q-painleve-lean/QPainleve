/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# A lower bound for the Krull dimension of formal power series rings

A power series ring over a nontrivial ring has Krull dimension at least the number
of its variables, by iterating the one-variable bound.
-/

public section

namespace MvPowerSeries

/-- The number of variables is a lower bound on the Krull dimension of the
formal power series ring over a nontrivial ring. -/
theorem le_ringKrullDim_fin (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d) R) := by
  induction d with
  | zero =>
      simpa only [Nat.cast_zero] using ringKrullDim_nonneg_of_nontrivial
        (R := MvPowerSeries (Fin 0) R)
  | succ d ih =>
      rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv R d).toRingEquiv, Nat.cast_succ]
      exact (add_le_add_left ih 1).trans ringKrullDim_succ_le_ringKrullDim_powerseries

end MvPowerSeries
