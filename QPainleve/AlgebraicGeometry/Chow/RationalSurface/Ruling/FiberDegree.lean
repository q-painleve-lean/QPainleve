/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Ruling.LineBundle

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cartier
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing

/-!
# Fiber-degree-one polarizations of rational rulings

For a flat ruling by projective lines on a smooth projective rational surface, a
single line bundle has degree one on every closed fiber. This supplies the line
bundle used to identify the ruling with a projective bundle in the classification
of minimal rational surfaces. See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)
local notation "P" => projectiveLine k
local notation "T" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) 1)

/-- A flat morphism from a smooth projective rational surface to the projective line
whose closed fibers are projective lines over the ground field admits a single line
bundle of degree one on all those fibers. -/
theorem exists_line_bundle_of_projectiveLine_fibers [X.Over S] [X.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [hRat : IsRationalOver (X ↘ S)]
    (f : X ⟶ P) [Flat f]
    (h : ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S) :
    ∃ L : InvertibleSheaf X, ∀ y : P, IsClosed ({y} : Set P) →
      ∃ e : P ≅ f.fiber y, e.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S ∧
        intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk L) = 1 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hclosed (y : P) (hy : IsClosed ({y} : Set P)) : IsClosedImmersion (f.fiberι y) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f ((projectiveLine k).fromSpecResidueField y)).flip inferInstance
  have hdeg (y : P) (hy : IsClosed ({y} : Set P)) (d : P ≅ f.fiber y)
      (hd : d.hom ≫ f.fiberι y ≫ X ↘ S = P ↘ S) (M : LineBundleClass X) :
      Chow.classIntersectionNumber k X M (pullback f T) =
        intersectionNumber k (d.hom ≫ f.fiberι y) M := by
    have := hclosed y hy
    have : (d.hom ≫ f.fiberι y).IsOver S := ⟨by rwa [Category.assoc]⟩
    obtain ⟨hI, hclass⟩ := f.exists_cartier_fiber_class_eq_pullback_twistingBundle hy
    have hker := ker_comp_of_isIso d.hom (f.fiberι y)
    let hJ : (d.hom ≫ f.fiberι y).ker.IsEffectiveCartier := hker ▸ hI
    rw [← hclass, ← mk_toInvertibleSheaf_congr hJ hI hker]
    exact Chow.classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker k hdim.le
      (d.hom ≫ f.fiberι y) (Scheme.IsCurveOver.topologicalKrullDim_eq_one k) hJ M
  obtain ⟨y, -, hy'⟩ :=
    nonempty_inter_closedPoints (Set.univ_nonempty (α := P)) isClosed_univ.isLocallyClosed
  have hy := mem_closedPoints_iff.mp hy'
  obtain ⟨e, he⟩ := h y hy
  obtain ⟨hI, hclass⟩ := f.exists_cartier_fiber_class_eq_pullback_twistingBundle hy
  have := hclosed y hy
  let a := e ≪≫ asIso (f.fiberι y).toImage
  have ha : a.hom ≫ (f.fiberι y).ker.subschemeι = e.hom ≫ f.fiberι y := by
    rw [Iso.trans_hom, asIso_hom, Category.assoc, (f.fiberι y).toImage_imageι]
  have : a.symm.hom.IsOver S := ⟨by
    rw [Iso.symm_hom, IdealSheafData.over_eq_subschemeι_comp, ← he,
      ← Category.assoc e.hom, ← ha, Category.assoc, a.inv_hom_id_assoc]⟩
  have hzero : Chow.classIntersectionNumber k X (pullback f T) (pullback f T) = 0 := by
    rw [hdeg y hy e he, intersectionNumber_pullback, Category.assoc, f.fiber_fac, ← Category.assoc]
    rw [intersectionNumber_def, ← pullback_comp,
      Subsingleton.elim (pullback ((projectiveLine k).fromSpecResidueField y) T) 1,
      pullback_one, eulerDegree_one]
  obtain ⟨L, hL⟩ := hI.exists_line_bundle_classIntersectionNumber_eq_one_of_projectiveLine
    a.symm (by simpa only [hclass] using hzero)
  refine ⟨L, fun z hz ↦ ?_⟩
  obtain ⟨d, hd⟩ := h z hz
  exact ⟨d, hd, (hdeg z hz d hd _).symm.trans (by simpa only [hclass] using hL)⟩

end AlgebraicGeometry.Scheme.Hom
