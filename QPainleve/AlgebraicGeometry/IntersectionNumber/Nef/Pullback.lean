/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage

/-!
# Pullback of nef line-bundle classes

The degree of a nef class on the image of a proper integral curve is nonnegative. The
degree on the original curve is zero if it maps to a point and a positive multiple of
the degree on its image otherwise. In particular, nef classes pull back to nef classes.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {C X Y : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k] [Y.Over (Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- A nef class has nonnegative degree along any morphism over the field from a proper
integral curve. -/
theorem IsNef.intersectionNumber_nonneg_of_isOver {a : LineBundleClass Y}
    (ha : IsNef k (Y ↘ Spec (.of k)) a) (i : C ⟶ Y) [i.IsOver (Spec (.of k))] :
    0 ≤ intersectionNumber k i a := by
  by_cases hi : Subsingleton i.image
  · rw [a.intersectionNumber_eq_zero_of_subsingleton_image i hi]
  have := i.isCurveOver_image_of_not_subsingleton (k := k) hi
  obtain ⟨n, _, hdeg⟩ :=
    i.exists_pos_intersectionNumber_eq_mul_of_not_subsingleton_image (k := k) hi
  rw [hdeg]
  exact mul_nonneg (Int.natCast_nonneg _) (ha.intersectionNumber_nonneg i.imageι
    (comp_over _ _).symm)

/-- Pullback along a morphism over the field preserves nefness. -/
theorem IsNef.pullback [X.Over (Spec (.of k))] {a : LineBundleClass Y}
    (ha : IsNef k (Y ↘ Spec (.of k)) a) (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    IsNef k (X ↘ Spec (.of k)) (LineBundleClass.pullback f a) :=
  (isNef_iff k _ _).mpr fun C _ _ i _ hi ↦ by
    have : i.IsOver (Spec (.of k)) := ⟨hi.symm⟩
    rw [intersectionNumber_pullback]
    exact ha.intersectionNumber_nonneg_of_isOver (i ≫ f)

end TauCeti.AlgebraicGeometry.LineBundleClass
