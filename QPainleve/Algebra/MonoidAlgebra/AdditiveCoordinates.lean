/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Additive coordinates for monoid algebra maps

The equivalence between additive and multiplicative monoid algebras commutes with maps of
exponents.
-/

public section

namespace AddMonoidAlgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  {M N : Type*} [AddMonoid M] [AddMonoid N]

/-- The additive-to-multiplicative monoid algebra equivalence is natural in the exponent monoid. -/
theorem toMultiplicativeAlgEquiv_comp_mapDomainAlgHom (f : M →+ N) :
    (toMultiplicativeAlgEquiv R A N).toAlgHom.comp (mapDomainAlgHom R A f) =
      (MonoidAlgebra.mapDomainAlgHom R A f.toMultiplicative).comp
        (toMultiplicativeAlgEquiv R A M).toAlgHom := by
  apply algHom_ext
  · intro m
    simp
  · ext a : 1
    simp

end AddMonoidAlgebra
