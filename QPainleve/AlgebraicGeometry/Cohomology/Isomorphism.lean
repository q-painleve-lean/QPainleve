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
  [f.IsOver (Spec (.of R))] {M N : Y.Modules} {M' N' : X.Modules}

/-- The cohomology comparison along a scheme isomorphism with a specified identification
of the pulled-back coefficient sheaf. -/
def cohomologyBaseLinearEquivOfPullbackIso (a : (pullback f).obj M ≅ M') (q : ℕ) :
    Cohomology M' q ≃ₗ[R] Cohomology M q :=
  (cohomologyBaseLinearEquivOfIso R a.symm q).trans
    (f.cohomologyPullbackBaseLinearEquivOfIsIso R M q)

/-- The comparison first identifies the coefficient sheaves and then transports the class
along the scheme isomorphism. -/
theorem cohomologyBaseLinearEquivOfPullbackIso_apply (a : (pullback f).obj M ≅ M') (q : ℕ)
    (x : Cohomology M' q) :
    f.cohomologyBaseLinearEquivOfPullbackIso R a q x =
      f.cohomologyPullbackBaseLinearEquivOfIsIso R M q
        (cohomologyMapBaseLinear R X a.inv q x) :=
  (congrArg _ (cohomologyBaseLinearEquivOfIso_apply R a.symm q x))

/-- The cohomology comparison commutes with a coefficient morphism and its
pullback under the specified coefficient identifications. -/
theorem cohomologyBaseLinearEquivOfPullbackIso_naturality (a : (pullback f).obj M ≅ M')
    (b : (pullback f).obj N ≅ N') (α : M ⟶ N) (q : ℕ) (x : Cohomology M' q) :
    f.cohomologyBaseLinearEquivOfPullbackIso R b q
        (cohomologyMapBaseLinear R X (a.inv ≫ (pullback f).map α ≫ b.hom) q x) =
      cohomologyMapBaseLinear R Y α q (f.cohomologyBaseLinearEquivOfPullbackIso R a q x) := by
  simp only [cohomologyBaseLinearEquivOfPullbackIso_apply, ← LinearMap.comp_apply,
    ← cohomologyMapBaseLinear_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [cohomologyMapBaseLinear_comp, LinearMap.comp_apply,
    cohomologyPullbackBaseLinearEquivOfIsIso_naturality]

end AlgebraicGeometry.Scheme.Hom
