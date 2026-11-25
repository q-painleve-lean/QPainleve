/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# Canonical cohomology under isomorphisms

An isomorphism over the base identifies canonical cohomology by the map on top
differential forms, following the base-linear cohomology pullback comparison.
-/

public noncomputable section

open CategoryTheory QPainleve
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (R : Type u) [CommRing R]
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
  (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (.of R))]

/-- Pullback along an isomorphism over the base induces an equivalence on the cohomology
of top forms in every degree. -/
def cohomologyCanonicalBundleLinearEquivOfIsIso (q : ℕ) :
    Cohomology (canonicalBundle R Y n).obj q ≃ₗ[R] Cohomology (canonicalBundle R X n).obj q :=
  (f.cohomologyPullbackBaseLinearEquivOfIsIso R (canonicalBundle R Y n).obj q).symm.trans
    (cohomologyBaseLinearEquivOfIso R (asIso (topDifferentialFormsMap R f n)) q)

/-- The equivalence on canonical cohomology applies the map on top differential forms
to the pullback cohomology class. -/
theorem cohomologyCanonicalBundleLinearEquivOfIsIso_apply (q : ℕ)
    (x : Cohomology (canonicalBundle R Y n).obj q) :
    f.cohomologyCanonicalBundleLinearEquivOfIsIso R n q x =
      cohomologyMapBaseLinear R X (topDifferentialFormsMap R f n) q
        ((f.cohomologyPullbackBaseLinearEquivOfIsIso R (canonicalBundle R Y n).obj q).symm x) := by
  exact cohomologyBaseLinearEquivOfIso_apply R (asIso (topDifferentialFormsMap R f n)) q _

end AlgebraicGeometry.Scheme.Hom
