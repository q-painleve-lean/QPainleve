/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
import QPainleve.AlgebraicGeometry.Curves.Degree.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# Pullback of nef line-bundle classes

The degree of a nef class on the image of a proper integral curve is nonnegative. The
degree on the original curve is zero if it maps to a point and a positive multiple of
the degree on its image otherwise. In particular, nef classes pull back to nef classes.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme

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
  have : IsProper (i ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : IsProper i := .of_comp i (Y ↘ Spec (.of k))
  have : IsProper i.toImage := by
    have : IsProper (i.toImage ≫ i.imageι) := by rw [i.toImage_imageι]; infer_instance
    exact .of_comp i.toImage i.imageι
  have : Surjective i.toImage :=
    ⟨i.toImage_surjective_of_isClosed_range i.isClosedMap.isClosed_range⟩
  have hdim : topologicalKrullDim i.image ≤ 1 :=
    (i.toImage.isClosedMap.specializingMap.topologicalKrullDim_le_of_surjective
      i.toImage.surjective).trans_eq (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := C) k)
  by_cases hpoint : Subsingleton i.image
  · rw [intersectionNumber_eq_zero_of_eq_comp k i i.toImage i.imageι
      i.toImage_imageι.symm (t := i.toImage (genericPoint C))
      (fun y ↦ specializes_of_eq (hpoint.elim y _)) a]
  have hpos : (0 : WithBot ℕ∞) < topologicalKrullDim i.image := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h ↦ hpoint
      (TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mp h))
    exact (WithBot.coe_le_coe.mpr (zero_le : (0 : ℕ∞) ≤ _)).trans
      (TauCeti.coheight_le_topologicalKrullDim (i.toImage (genericPoint C)))
  have hproper : IsProper (i.image ↘ Spec (.of k)) := by
    have : IsProper (i.toImage ≫ i.image ↘ Spec (.of k)) := by
      rw [comp_over]
      infer_instance
    have : UniversallyClosed (i.image ↘ Spec (.of k)) :=
      UniversallyClosed.of_comp_surjective i.toImage _
    have : IsSeparated (i.image ↘ Spec (.of k)) := by
      rw [← comp_over i.imageι (Spec (.of k))]
      infer_instance
    have : LocallyOfFiniteType (i.image ↘ Spec (.of k)) := by
      rw [← comp_over i.imageι (Spec (.of k))]
      infer_instance
    exact {}
  have : i.image.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, hproper, hdim.antisymm (le_of_not_gt fun hlt ↦
      (not_le.mpr hpos) ((ENat.WithBot.lt_add_one_iff (m := 0)).mp (by simpa using hlt)))⟩
  obtain ⟨n, _, hn⟩ := exists_pos_eulerDegree_pullback (k := k) i.toImage
  rw [← i.toImage_imageι, ← intersectionNumber_pullback, intersectionNumber_def, hn,
    ← intersectionNumber_def]
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
