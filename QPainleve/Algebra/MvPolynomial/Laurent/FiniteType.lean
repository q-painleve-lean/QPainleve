/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

/-!
# Finite type Laurent polynomial algebras

The exponents of a Laurent ring on finitely many variables form a finitely generated
abelian group, so the Laurent ring is a finite type algebra over its coefficient ring.
-/

public section

namespace TauCeti.LaurentRing

/-- A Laurent polynomial algebra in finitely many variables is of finite type. -/
instance {R ι : Type*} [CommRing R] [Finite ι] : Algebra.FiniteType R (LaurentRing R ι) := by
  have : AddGroup.FG (ι →₀ ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have : AddMonoid.FG (ι →₀ ℤ) := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  infer_instance

end TauCeti.LaurentRing
