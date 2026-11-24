/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Image
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
import QPainleve.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Degrees along maps of curves

The degree of a line-bundle class along a curve mapping to a point is zero.
Otherwise it is a positive multiple of the degree on the image curve.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {C Y : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k]

/-- Every line-bundle class has degree zero along a curve with single-point image. -/
theorem intersectionNumber_eq_zero_of_subsingleton_image (a : LineBundleClass Y) (i : C ⟶ Y)
    (hi : Subsingleton i.image) : intersectionNumber k i a = 0 :=
  intersectionNumber_eq_zero_of_eq_comp k i i.toImage i.imageι
    i.toImage_imageι.symm (t := i.toImage (genericPoint C))
    (fun y ↦ specializes_of_eq (hi.elim y _)) a

end TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry LineBundleClass

variable {k : Type u} [Field k] {C Y : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k] [Y.Over (Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- Along a nonconstant map of a proper integral curve the degree is a fixed positive
multiple of the degree on its scheme-theoretic image. -/
theorem exists_pos_intersectionNumber_eq_mul_of_not_subsingleton_image (i : C ⟶ Y)
    [i.IsOver (Spec (.of k))] (hi : ¬ Subsingleton i.image) :
    ∃ n : ℕ, 0 < n ∧ ∀ a : LineBundleClass Y,
      intersectionNumber k i a = n * intersectionNumber k i.imageι a := by
  have : IsProper (i ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : IsProper i := .of_comp i (Y ↘ Spec (.of k))
  have := i.isCurveOver_image_of_not_subsingleton (k := k) hi
  obtain ⟨n, hn, hdeg⟩ := exists_pos_eulerDegree_pullback (k := k) i.toImage
  refine ⟨n, hn, fun a ↦ ?_⟩
  calc
    intersectionNumber k i a = intersectionNumber k (i.toImage ≫ i.imageι) a :=
      congrArg (fun j ↦ intersectionNumber k j a) i.toImage_imageι.symm
    _ = n * intersectionNumber k i.imageι a := by
      rw [← intersectionNumber_pullback, intersectionNumber_def, hdeg, ← intersectionNumber_def]

end AlgebraicGeometry.Scheme.Hom
