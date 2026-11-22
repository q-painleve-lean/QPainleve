/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Group algebras of free abelian groups

The unique-sums property of integral basis coordinates makes the group algebra of a free
abelian group over a domain a domain.
-/

public section

namespace AddMonoidAlgebra

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [IsDomain k]
  [AddCommGroup B] [Module ℤ B] [Module.Free ℤ B]

/-- The group algebra of a free abelian group over a domain is a domain. -/
instance instIsDomainOfFreeInt : IsDomain (AddMonoidAlgebra k B) := by
  let b := Module.Free.chooseBasis ℤ B
  let : UniqueSums B := b.repr.toAddEquiv.uniqueSums_iff.mpr inferInstance
  infer_instance

end AddMonoidAlgebra
