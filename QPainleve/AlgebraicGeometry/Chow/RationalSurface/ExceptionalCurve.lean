/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Exceptional prime curves on rational surfaces

Arithmetic adjunction detects exceptional curves of the first kind from their
self-intersection and canonical degree. In particular a Picard isometry preserving
the canonical class preserves exceptionality on the prime curves it matches.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry.LineBundleClass

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]

/-- A prime curve on a smooth projective rational surface is exceptional of the
first kind exactly when its square and its intersection with the canonical class
are both `-1`. -/
theorem isExceptionalCurveOfFirstKind_iff_primeDivisorClass (p : CodimensionOnePoint X) :
    let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X :=
      (inferInstance : Scheme.IsRationalOver (X ↘ Spec (.of k))).isIntegral_of_smooth
    let J := vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
    let a := primeDivisorClass p
    J.IsExceptionalCurveOfFirstKind ↔ classIntersectionNumber k X a a = -1 ∧
      classIntersectionNumber k X a (mk (canonicalBundle k X 2)) = -1 := by
  intro _ _ _ _ J a
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  have hJ : J.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  let : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  let : J.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have hnum := hJ.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    (k := k) hX.le
  have hclass : a = (mk hJ.toInvertibleSheaf)⁻¹ := by simp only [a, primeDivisorClass_def]
  have hadj : 2 * (J.subscheme.genus k : ℤ) - 2 =
      classIntersectionNumber k X a a +
        classIntersectionNumber k X a (mk (canonicalBundle k X 2)) :=
    two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  dsimp only at hnum
  rw [← hclass] at hnum
  rw [hnum]
  omega

end TauCeti.AlgebraicGeometry.Chow
