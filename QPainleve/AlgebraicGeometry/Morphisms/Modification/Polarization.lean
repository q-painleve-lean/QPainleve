/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
public import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.Curves.Image

/-!
# Exceptional curves and pullbacks of ample classes

A prime curve on a proper surface is contracted by a modification to a
normal surface exactly when the pullback of an ample class has degree zero on it.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {V Z : Scheme.{u}}
  [V.Over (Spec (.of k))] [IsProper (V ↘ Spec (.of k))] [IsIntegral V]
  [Z.Over (Spec (.of k))] [IsIntegral Z] [IsNormalScheme Z]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)

/-- A prime curve on a proper surface is exceptional for a modification to a normal
surface exactly when the pullback of an ample class from the target has degree zero on it. -/
theorem mem_centre_iff_intersectionNumber_pullback_eq_zero
    (f : V ⟶ Z) [IsModification f] [f.IsOver S] (hV : topologicalKrullDim V = 2)
    (hZ : topologicalKrullDim Z ≤ 2) (p : CodimensionOnePoint V)
    {a : LineBundleClass Z} (ha : a.IsAmple) :
    f p.val ∈ f.centre ↔
      intersectionNumber k (vanishingIdeal ⟨closure {p.val}, isClosed_closure⟩).subschemeι
        (pullback f a) = 0 := by
  let I := vanishingIdeal (X := V) ⟨closure {p.val}, isClosed_closure⟩
  let i := I.subschemeι
  let j := i ≫ f
  have : IsProper (I.subscheme ↘ S) := by
    rw [IdealSheafData.over_eq_subschemeι_comp]
    infer_instance
  have : IsIntegral I.subscheme :=
    isIntegral_subscheme_vanishingIdeal_closure_singleton p.val
  have : IsProper j := inferInstanceAs (IsProper (i ≫ f))
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hV p⟩
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ S)
  have hi : Set.range i = closure {p.val} := by
    rw [I.range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk]
  obtain ⟨q, hq⟩ : p.val ∈ Set.range i := hi ▸ (subset_closure (Set.mem_singleton _))
  have : j.IsOver S := inferInstanceAs ((i ≫ f).IsOver S)
  have hr : Set.range j.imageι = Set.range j := by
    rw [j.range_imageι, j.isClosedMap.isClosed_range.closure_eq]
  have hpoint : Subsingleton j.image ↔ (Set.range j).Subsingleton := by
    rw [← hr]
    exact ⟨fun h ↦ @Set.subsingleton_range _ _ h _, fun h ↦
      ⟨fun x y ↦ j.imageι.isEmbedding.injective (h (Set.mem_range_self x) (Set.mem_range_self y))⟩⟩
  rw [intersectionNumber_pullback, ha.intersectionNumber_eq_zero_iff_subsingleton_image j, hpoint]
  constructor
  · intro hp
    have hc := mem_closedPoints_iff.mp (f.centre_subset_closedPoints hZ hp)
    refine (Set.subsingleton_singleton (a := f p.val)).anti ?_
    rintro _ ⟨x, rfl⟩
    have hx : i x ∈ closure {p.val} := hi ▸ Set.mem_range_self x
    rw [Scheme.Hom.comp_apply]
    exact ((specializes_iff_mem_closure.mpr hx).map f.continuous).mem_closed hc rfl
  · intro hj
    by_contra hp
    have hmem (x : I.subscheme) : f (i x) ∈ f.isoLocus := by
      have he : f (i x) = f p.val := by
        simpa only [j, Scheme.Hom.comp_apply, hq] using
          hj (Set.mem_range_self x) (Set.mem_range_self q)
      rw [he]
      simpa only [f.centre_def, Set.mem_compl_iff, SetLike.mem_coe, not_not] using hp
    have : Subsingleton I.subscheme := ⟨fun x y ↦ i.isEmbedding.injective
      (f.injOn_preimage_isoLocus (hmem x) (hmem y)
        (hj (Set.mem_range_self x) (Set.mem_range_self y)))⟩
    have hdim := TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr this
    rw [Scheme.IsCurveOver.topologicalKrullDim_eq_one k] at hdim
    contradiction

end AlgebraicGeometry.Scheme.Hom
