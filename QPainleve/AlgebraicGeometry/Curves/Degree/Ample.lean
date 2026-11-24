/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Positive degree of ample classes on proper integral curves

An ample class has a positive power cut out by a nonempty effective Cartier divisor.
Its degree is the rank of the finite divisor, and degree is additive under tensor
product. This is the forward implication of
[Stacks Project, Lemma 33.44.14](https://stacks.math.columbia.edu/tag/0B5X).
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple

variable {X : Scheme.{u}} {k : Type u} [Field k] {a : LineBundleClass X}

variable [X.Over (Spec (.of k))] [X.IsCurveOver k] in
/-- An ample line-bundle class on a proper integral curve has strictly positive Euler degree.
The curve may be singular. -/
theorem eulerDegree_pos (ha : a.IsAmple) : 0 < a.eulerDegree k := by
  let f := X ↘ Spec (.of k)
  have hdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k
  obtain ⟨n, hn, I, hI, hne, hclass⟩ :=
    ha.exists_effectiveCartier_pow_ne_top f (hdim.symm ▸ zero_lt_one)
  have : RelativeDimensionLE 1 f := (relativeDimensionLE_iff_of_field f).mpr hdim.le
  have : IsFinite (I.subschemeι ≫ f) := hI.isFinite_subschemeι_comp
  have hdegree := hI.eulerDegree_inv_mk_toInvertibleSheaf k I default
  rw [hclass] at hdegree
  have hnonempty : Nonempty I.subscheme := by
    by_contra! hempty
    exact hne (I.ker_subschemeι ▸ (Scheme.Hom.ker_eq_top_iff_isEmpty I.subschemeι).mpr hempty)
  have hpos : 0 < (I.subschemeι ≫ f).finrank default := by
    obtain ⟨x⟩ := hnonempty
    exact Nat.pos_of_ne_zero fun hz ↦
      ((Scheme.Hom.finrank_eq_zero_iff_notMem_range _ _).mp hz)
        ⟨x, Subsingleton.elim _ _⟩
  rw [← zpow_natCast, eulerDegree_zpow_of_isCurveOver] at hdegree
  exact pos_of_mul_pos_right (hdegree.symm ▸ Int.natCast_pos.mpr hpos) (Int.natCast_nonneg n)

/-- An ample class has positive degree on every integral closed curve. -/
theorem intersectionNumber_pos (ha : a.IsAmple)
    {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
    (i : C ⟶ X) [IsClosedImmersion i] :
    0 < intersectionNumber k i a := by
  rw [intersectionNumber_def]
  exact (ha.pullback_of_isAffineHom i).eulerDegree_pos

variable {C : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k] [X.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- The degree of an ample class along a proper integral curve vanishes exactly when
its scheme-theoretic image is a point. -/
theorem intersectionNumber_eq_zero_iff_subsingleton_image
    (ha : a.IsAmple) (i : C ⟶ X) [i.IsOver (Spec (.of k))] :
    intersectionNumber k i a = 0 ↔ Subsingleton i.image := by
  refine ⟨fun h ↦ ?_, fun hi ↦ ?_⟩
  · by_contra hi
    have := i.isCurveOver_image_of_not_subsingleton (k := k) hi
    obtain ⟨n, hn, hdeg⟩ :=
      i.exists_pos_intersectionNumber_eq_mul_of_not_subsingleton_image (k := k) hi
    rw [hdeg] at h
    exact (mul_pos (Int.natCast_pos.mpr hn) (ha.intersectionNumber_pos i.imageι)).ne' h
  · exact a.intersectionNumber_eq_zero_of_subsingleton_image i hi

/-- An ample class has nonnegative degree along every closed integral curve over
the base field. -/
theorem isNef {f : X ⟶ Spec (.of k)} (ha : a.IsAmple) : IsNef k f a :=
  (isNef_iff k f a).mpr fun _ _ _ i _ _ ↦ (ha.intersectionNumber_pos i).le

end TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple
