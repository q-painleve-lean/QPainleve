/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Factorial stalks of affine schemes

A stalk of the spectrum of a factorial ring is factorial, since it is the localization
of the coordinate ring at the corresponding prime.
-/

public section

namespace AlgebraicGeometry

/-- Stalks of the spectrum of a factorial ring are factorial. -/
theorem uniqueFactorizationMonoid_stalk_Spec (R : CommRingCat) [UniqueFactorizationMonoid R]
    (x : Spec R) : UniqueFactorizationMonoid ((Spec R).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact UniqueFactorizationMonoid.of_isLocalization x.asIdeal.primeCompl _

end AlgebraicGeometry
