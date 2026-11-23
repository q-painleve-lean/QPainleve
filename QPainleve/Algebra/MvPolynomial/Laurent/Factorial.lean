/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Unique factorization in Laurent polynomial rings

The localization `TauCeti.LaurentRing.isLocalization` lets us apply
`UniqueFactorizationMonoid.of_isLocalization` to the multivariable polynomial ring.
This works for any variable type.
-/

public section

namespace TauCeti.LaurentRing

/-- Laurent polynomials in any family of variables inherit unique factorization from the
coefficient ring. -/
instance {R K : Type*} [CommRing R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (LaurentRing R K) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.closure (Set.range (MvPolynomial.X : K → MvPolynomial K R))) (LaurentRing R K)

end TauCeti.LaurentRing
