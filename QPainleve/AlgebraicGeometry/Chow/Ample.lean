/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Intersections with ample classes on surfaces

An ample class has positive intersection with each integral curve on a projective
surface. Expanding a nonempty effective Cartier divisor from a positive power of a
second ample class gives positive intersection of the two ample classes. In
particular an ample class has positive square, as required by the numerical
criterion for ampleness and by the choice of a positive cone component.
An ample class also has nonnegative intersection with every nef class.

See the [Stacks Project, Lemma 33.45.9](https://stacks.math.columbia.edu/tag/0BEV)
for the numerical positivity of ample intersections.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] {a b : LineBundleClass X}

/-- Intersecting an ample class with any prime divisor of a locally factorial projective
surface gives a strictly positive integer. -/
theorem classIntersectionNumber_primeDivisorClass_pos_of_isAmple
    (hX : topologicalKrullDim X = 2) (ha : a.IsAmple) (p : CodimensionOnePoint X) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    0 < classIntersectionNumber k X a (LineBundleClass.primeDivisorClass p) := by
  intro _
  let I := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  rw [classIntersectionNumber_primeDivisorClass_eq_intersectionNumber k hX]
  exact ha.intersectionNumber_pos I.subschemeι

/-- An ample class has positive intersection with any nonzero effective Weil divisor. -/
theorem classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple [IsNoetherian X]
    (hX : topologicalKrullDim X = 2) (ha : a.IsAmple)
    {D : SchemeWeilDivisor X} (hD : 0 ≤ D) (hne : D ≠ 0) :
    0 < classIntersectionNumber k X a
      (Scheme.CartierDivisor.weilToLineBundleClassHom X D).toMul := by
  rw [classIntersectionNumber_weilToLineBundleClassHom k hX]
  refine Finsupp.sum_pos (fun p hp ↦ ?_) hne
  exact mul_pos (lt_of_le_of_ne (hD p) (Finsupp.mem_support_iff.mp hp).symm)
    (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX ha p)

/-- Two ample classes on a locally factorial integral projective surface have positive
intersection. Taking the same class twice gives positivity of its square. -/
theorem classIntersectionNumber_pos_of_isAmple (hX : topologicalKrullDim X = 2)
    (ha : a.IsAmple) (hb : b.IsAmple) : 0 < classIntersectionNumber k X a b := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have hdim : 0 < topologicalKrullDim X := by rw [hX]; decide
  obtain ⟨n, D, -, hE, hne, hDclass⟩ :=
    hb.exists_effectiveWeilDivisor_pow_eq (X ↘ Spec (.of k)) hdim
  have hpow : 0 < classIntersectionNumber k X a (b ^ n) := by
    rw [← hDclass]
    exact classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k hX ha hE hne
  rw [classIntersectionNumber_pow_right k hX] at hpow
  exact pos_of_mul_pos_right hpow (Int.natCast_nonneg n)

end TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] {a h : LineBundleClass X}

/-- The intersection of a nef class with an ample class is nonnegative. -/
theorem IsNef.classIntersectionNumber_nonneg_of_isAmple
    (ha : a.IsNef k (X ↘ Spec (.of k))) (hX : topologicalKrullDim X = 2)
    (hh : h.IsAmple) : 0 ≤ Chow.classIntersectionNumber k X a h := by
  have hdim : 0 < topologicalKrullDim X := by rw [hX]; decide
  obtain ⟨n, hn, I, hI, _, hclass⟩ :=
    hh.exists_effectiveCartier_pow_ne_top (X ↘ Spec (.of k)) hdim
  have hnonneg := Chow.classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hX ha hI
  rw [hclass, Chow.classIntersectionNumber_pow_right k hX] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg (Int.natCast_pos.mpr hn)

end TauCeti.AlgebraicGeometry.LineBundleClass
