/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.Curves.GenusZero
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Numerical recognition of exceptional curves

An integral effective Cartier curve over an algebraically closed field is exceptional
of the first kind exactly when it has arithmetic genus zero and self-intersection `-1`.
The self-intersection can be read as the degree of its normal bundle or as the square of
its class on a projective surface. This gives the input to Castelnuovo contraction
from arithmetic adjunction. See Hacking, *Compact Complex Surfaces*, §7.5.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {I : X.IdealSheafData}

/-- A Cartier curve over an algebraically closed field is exceptional of the first kind
exactly when its arithmetic genus is zero and its normal bundle has degree `-1`. -/
theorem isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_intersectionNumber
    [I.subscheme.Over (Spec (.of k))] [I.subscheme.IsCurveOver k] (hI : I.IsEffectiveCartier) :
    I.IsExceptionalCurveOfFirstKind ↔ I.subscheme.genus k = 0 ∧
      LineBundleClass.intersectionNumber k I.subschemeι
        (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = -1 := by
  constructor
  · intro hE
    have hgen : I.subscheme.genus k = 0 := by
      simpa only [genus_def] using hE.finrank_cohomology_one_trivial_eq_zero k
    obtain ⟨e, he⟩ := genus_eq_zero_iff_exists_iso_projectiveLine.mp hgen
    have : e.hom.IsOver (Spec (.of k)) := he
    refine ⟨hgen, ?_⟩
    rw [hE.intersectionNumber_self k, e.hom.finrank_cohomology_trivial_of_isIso k 0,
      (projectiveLine.cohomologyZeroTrivialLinearEquiv k).finrank_eq, Module.finrank_self,
      Nat.cast_one]
  · rintro ⟨hgen, hdeg⟩
    obtain ⟨e, he⟩ := genus_eq_zero_iff_exists_iso_projectiveLine.mp hgen
    have : e.hom.IsOver (Spec (.of k)) := he
    have : e.inv.IsOver (Spec (.of k)) :=
      ⟨by rw [← comp_over e.hom (Spec (.of k)), e.inv_hom_id_assoc]⟩
    refine isExceptionalCurveOfFirstKind_iff_intersectionNumber.mpr ⟨hI, k, inferInstance,
      e.symm, ?_⟩
    rw [LineBundleClass.intersectionNumber_def, Iso.symm_hom, ← LineBundleClass.pullback_comp,
      LineBundleClass.eulerDegree_pullback_of_isIso e.inv (comp_over e.inv _)]
    simpa only [LineBundleClass.intersectionNumber_def] using hdeg

/-- On a projective scheme of dimension at most two, the normal bundle degree of an integral
Cartier curve can be replaced by the self-intersection of its class in the surface pairing. -/
theorem isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [I.subscheme.IsCurveOver k]
    (hX : topologicalKrullDim X ≤ 2) (hI : I.IsEffectiveCartier) :
    let a := (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
    I.IsExceptionalCurveOfFirstKind ↔
      I.subscheme.genus k = 0 ∧ Chow.classIntersectionNumber k X a a = -1 := by
  dsimp only
  rw [Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hX hI
    (IsCurveOver.topologicalKrullDim_eq_one k)]
  exact hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_intersectionNumber

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
