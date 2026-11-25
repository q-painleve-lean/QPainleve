/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Evaluation of split torus characters

The values of a character on the coordinate basis give the torus point at which
evaluating any exponent vector recovers the character.
-/

public section

open Multiplicative

namespace TauCeti

/-- Evaluation at the basis values of a character agrees with the character on every
integral exponent vector. -/
theorem torusCharacter_of_pi_single {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (c : Multiplicative (ι → ℤ) →* Rˣ) (x : ι → ℤ) :
    torusCharacter (fun j ↦ c (ofAdd (Pi.single j 1))) x = c (ofAdd x) := by
  conv_rhs => rw [pi_eq_sum_univ' x, ofAdd_sum, map_prod]
  simp only [torusCharacter_def, ofAdd_zsmul, map_zpow]

end TauCeti
