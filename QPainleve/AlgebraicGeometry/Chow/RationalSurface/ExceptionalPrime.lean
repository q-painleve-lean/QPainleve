/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Exceptional prime divisors on rational surfaces

Arithmetic adjunction recognizes a prime divisor as a first-kind exceptional
curve from its square and canonical degree. This supplies the criterion for
transporting an already identified prime under a Picard isometry.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData TauCeti.AlgebraicGeometry.LineBundleClass

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- A prime divisor on a smooth projective rational surface is exceptional of the
first kind exactly when its self-intersection and canonical degree are both `-1`. -/
theorem isExceptionalCurveOfFirstKind_vanishingIdeal_iff (p : CodimensionOnePoint X) :
    (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).IsExceptionalCurveOfFirstKind ↔
      classIntersectionNumber k X (primeDivisorClass p) (primeDivisorClass p) = -1 ∧
      classIntersectionNumber k X (primeDivisorClass p)
        (mk (canonicalBundle k X 2)) = -1 := by
  let I := vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) (n := 2)
  let : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  let : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hadj : 2 * (I.subscheme.genus k : ℤ) - 2 =
      classIntersectionNumber k X (primeDivisorClass p) (primeDivisorClass p) +
        classIntersectionNumber k X (primeDivisorClass p) (mk (canonicalBundle k X 2)) :=
    two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hnum :=
    hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber (k := k) hX.le
  dsimp only at hnum
  rw [← primeDivisorClass_def p] at hnum
  rw [hnum]
  constructor
  · rintro ⟨hg, hsq⟩
    rw [hg, hsq] at hadj
    exact ⟨hsq, by omega⟩
  · rintro ⟨hsq, hK⟩
    rw [hsq, hK] at hadj
    exact ⟨by omega, hsq⟩

end TauCeti.AlgebraicGeometry.Chow
