/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Invariance of surface intersection under isomorphism

The Euler characteristic and the resulting intersection pairing commute with
pullback along scheme isomorphisms over the coefficient field. This lets one
compare the Picard pairings computed in different models of the same surface.
On smooth surfaces the canonical class also pulls back, giving invariance
of the Riemann–Roch equation for a line bundle.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [IsIso f] [f.IsOver (Spec (.of k))]

/-- Pullback along an isomorphism preserves the truncated Euler characteristic of a
line-bundle class, for every cutoff. -/
theorem LineBundleClass.eulerCharBelow_pullback_of_isIso (a : LineBundleClass Y) (q : ℕ) :
    eulerCharBelow k (pullback f a) q = eulerCharBelow k a q := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerCharBelow_mk, eulerCharBelow_mk, InvertibleSheaf.pullback_obj_obj,
    Scheme.Hom.eulerCharBelow_pullback_of_isIso]

/-- Pullback along an isomorphism preserves the Euler-characteristic intersection pairing. -/
theorem Chow.classIntersectionNumber_pullback_of_isIso (a b : LineBundleClass Y) :
    classIntersectionNumber k X (LineBundleClass.pullback f a) (LineBundleClass.pullback f b) =
      classIntersectionNumber k Y a b := by
  simp only [classIntersectionNumber_eq, ← LineBundleClass.pullback_inv,
    ← LineBundleClass.pullback_mul, LineBundleClass.eulerCharBelow_pullback_of_isIso k f,
    ← LineBundleClass.pullback_one f]

namespace LineBundleClass

open QPainleve

variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]

/-- The doubled Riemann–Roch equation for the pullback of a line bundle along a surface
isomorphism is equivalent to the equation for the original line bundle. -/
theorem eulerCharBelow_eq_riemannRoch_pullback_iff_of_isIso (a : LineBundleClass Y) :
    let KX := mk (canonicalBundle k X 2)
    let KY := mk (canonicalBundle k Y 2)
    let B := Chow.classIntersectionNumber k X
    let C := Chow.classIntersectionNumber k Y
    let b := pullback f a
    2 * (eulerCharBelow k b 3 - eulerCharBelow k (1 : LineBundleClass X) 3) =
      B b b - B b KX ↔
    2 * (eulerCharBelow k a 3 - eulerCharBelow k (1 : LineBundleClass Y) 3) =
      C a a - C a KY := by
  have hK : pullback f (mk (canonicalBundle k Y 2)) = mk (canonicalBundle k X 2) := by
    rw [pullback_mk, mk_pullback_canonicalBundle]
  dsimp only
  rw [← hK, ← pullback_one f]
  simp only [eulerCharBelow_pullback_of_isIso, Chow.classIntersectionNumber_pullback_of_isIso]

end LineBundleClass

end TauCeti.AlgebraicGeometry
