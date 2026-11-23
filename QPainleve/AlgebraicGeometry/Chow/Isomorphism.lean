/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Invariance of surface intersection under isomorphism

The Euler characteristic and the resulting intersection pairing commute with
pullback along scheme isomorphisms over the coefficient field. This lets one
compare the Picard pairings computed in different models of the same surface.
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

end TauCeti.AlgebraicGeometry
