/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# Images of proper integral curves

The scheme-theoretic image of a nonconstant map from a proper integral curve to a
separated scheme locally of finite type over the field is a proper integral curve.
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {C Y : Scheme.{u}}
  [C.Over (Spec (.of k))] [C.IsCurveOver k] [Y.Over (Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- A morphism from a proper integral curve over a field is proper into a separated
scheme over the field, and its scheme-theoretic image is a curve if it has more than one point. -/
theorem isCurveOver_image_of_not_subsingleton (i : C ⟶ Y) [i.IsOver (Spec (.of k))]
    (hpoint : ¬ Subsingleton i.image) : i.image.IsCurveOver k := by
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
  exact Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, hproper, hdim.antisymm (le_of_not_gt fun hlt ↦
      (not_le.mpr hpos) ((ENat.WithBot.lt_add_one_iff (m := 0)).mp (by simpa using hlt)))⟩

end AlgebraicGeometry.Scheme.Hom
