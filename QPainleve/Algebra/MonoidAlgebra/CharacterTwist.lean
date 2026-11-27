/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv
import TauCeti.Algebra.MonoidAlgebra.CharacterTwist

/-!
# Character twists of additive monoid algebras

The existing character twist of a multiplicative monoid algebra transports
through the equivalence between the two exponent notations.
-/

public noncomputable section

namespace AddMonoidAlgebra

open Multiplicative

variable {R M : Type*} [CommSemiring R] [AddMonoid M]

/-- The algebra automorphism scaling an additive monomial by its character value. -/
def charTwist (χ : Multiplicative M →* Rˣ) : AddMonoidAlgebra R M ≃ₐ[R] AddMonoidAlgebra R M :=
  let e := toMultiplicativeAlgEquiv R R M
  e.trans ((MonoidAlgebra.charTwist χ).trans e.symm)

/-- A character twist scales the coefficient of each monomial. -/
@[simp]
theorem charTwist_single (χ : Multiplicative M →* Rˣ) (m : M) (r : R) :
    charTwist χ (single m r) = single m ((χ (ofAdd m) : R) * r) := by
  rw [charTwist, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    toMultiplicativeAlgEquiv_single, MonoidAlgebra.charTwist_single,
    toMultiplicativeAlgEquiv_symm_single, toAdd_ofAdd]

end AddMonoidAlgebra
