/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.LineBundle.Ample

import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Positive intersections of ample classes on surfaces

An ample class has positive intersection with each integral curve on a projective
surface. Expanding a nonempty effective Cartier divisor from a positive power of a
second ample class gives positive intersection of the two ample classes. In
particular an ample class has positive square, as required by the numerical
criterion for ampleness and by the choice of a positive cone component.

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
  let f := classIntersectionBilinForm k hX (Additive.ofMul a)
  have he : classIntersectionNumber k X a (b ^ n) = (n : ℤ) * classIntersectionNumber k X a b := by
    simpa only [f, classIntersectionBilinForm_apply, toMul_zsmul, toMul_ofMul,
      Int.zsmul_eq_mul, zpow_natCast] using f.map_smul (n : ℤ) (Additive.ofMul b)
  exact pos_of_mul_pos_right (he ▸ hpow) (Int.natCast_nonneg n)

end TauCeti.AlgebraicGeometry.Chow
