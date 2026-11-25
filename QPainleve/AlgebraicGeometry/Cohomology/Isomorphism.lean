/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear

/-!
# Cohomology under scheme and coefficient isomorphisms

A scheme isomorphism over a base ring induces a cohomology equivalence with
a specified model for the pulled-back coefficient sheaf.
-/

public noncomputable section

open CategoryTheory TauCeti
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))] {M : Y.Modules} {M' : X.Modules}

/-- The cohomology comparison along a scheme isomorphism with a specified identification
of the pulled-back coefficient sheaf. -/
def cohomologyBaseLinearEquivOfPullbackIso (a : (pullback f).obj M ≅ M') (q : ℕ) :
    Cohomology M' q ≃ₗ[R] Cohomology M q :=
  (cohomologyBaseLinearEquivOfIso R a.symm q).trans
    (f.cohomologyPullbackBaseLinearEquivOfIsIso R M q)

end AlgebraicGeometry.Scheme.Hom
