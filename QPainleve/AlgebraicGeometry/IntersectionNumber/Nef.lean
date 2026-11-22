/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.Curves.Basic
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Nef line-bundle classes

Nefness tests the degree on every proper closed integral curve, including singular curves.
On a proper scheme this is the nonnegativity version of Tau Ceti's
`LineBundleClass.NumericallyTrivial`.

## References

* O. Debarre, *Introduction to Mori Theory*, §4.2.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k))

/-- A line-bundle class is nef if its degree on each proper closed integral curve over the field
is nonnegative. -/
public def IsNef (a : LineBundleClass X) : Prop :=
  ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [C.IsCurveOver k] (i : C ⟶ X)
    [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x → 0 ≤ intersectionNumber k i a

/-- Nefness is nonnegativity of restriction degrees on proper closed integral curves. -/
public theorem isNef_iff (a : LineBundleClass X) :
    IsNef k x a ↔
      ∀ (C : Scheme.{u}) [C.Over (Spec (.of k))] [C.IsCurveOver k] (i : C ⟶ X)
        [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ x → 0 ≤ intersectionNumber k i a :=
  (Iff.rfl)

variable {k x} in
/-- A nef class has nonnegative degree on each proper closed integral curve. -/
public theorem IsNef.intersectionNumber_nonneg {a : LineBundleClass X} (ha : IsNef k x a)
    {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
    (i : C ⟶ X) [IsClosedImmersion i]
    (hi : C ↘ Spec (.of k) = i ≫ x) :
    0 ≤ intersectionNumber k i a :=
  (isNef_iff k x a).mp ha C i hi

/-- The trivial line-bundle class is nef. -/
@[simp]
public theorem isNef_one : IsNef k x (1 : LineBundleClass X) :=
  (isNef_iff k x _).mpr fun _ _ _ i _ _ ↦ (intersectionNumber_one k i).symm ▸ le_rfl

variable {k x} in
/-- The tensor product of nef classes is nef. -/
public theorem IsNef.mul {a b : LineBundleClass X}
    (ha : IsNef k x a) (hb : IsNef k x b) : IsNef k x (a * b) :=
  (isNef_iff k x _).mpr fun C _ _ i _ hi ↦ by
    have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
      (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
    rw [intersectionNumber_mul_of_isIntegral]
    exact add_nonneg (ha.intersectionNumber_nonneg i hi) (hb.intersectionNumber_nonneg i hi)

end TauCeti.AlgebraicGeometry.LineBundleClass
