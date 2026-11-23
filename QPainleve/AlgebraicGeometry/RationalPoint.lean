/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ResidueDegree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Residue degrees at rational points

The residue degree over an algebraically closed field is one at a closed point of
a scheme locally of finite type. The comparison uses Mathlib's `pointOfClosedPoint`.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Closed points of a scheme locally of finite type over an algebraically closed
field have residue degree one. -/
public theorem residueDegree_eq_one_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed {x}) : f.residueDegree x = 1 := by
  simpa only [pointOfClosedPoint_apply] using
    TauCeti.AlgebraicGeometry.residueDegree_eq_one_of_section
      (pointOfClosedPoint_comp f x hx) (default : Spec (.of k))

end AlgebraicGeometry.Scheme.Hom
