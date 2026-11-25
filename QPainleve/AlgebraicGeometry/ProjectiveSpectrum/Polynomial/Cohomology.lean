/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Cohomology.Isomorphism

/-!
# Cohomology of polynomial and symmetric-algebra twists

A basis identifies the cohomology of each twisting sheaf on polynomial projective space
with the cohomology of the corresponding twist on the projective spectrum of the symmetric
algebra. The comparison applies in every cohomological degree over the coefficient ring.
-/

open AlgebraicGeometry AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace Module.Basis

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type (max u v)} [CommRing R] [AddCommMonoid M] [Module R M] {ι : Type v}

variable [base : Scheme.Over (Proj (MvPolynomial.homogeneousSubmodule ι R)) (Spec (.of R))]

/-- The basis comparison identifies the cohomology of corresponding twists. -/
public noncomputable def cohomologyPolynomialTwistingSheafLinearEquiv
    (b : Basis ι R M)
    (hOver : Proj (MvPolynomial.homogeneousSubmodule ι R) ↘ Spec (.of R) =
      toSpecCoeff (MvPolynomial.homogeneousSubmodule ι R)) (m : ℤ) (q : ℕ) :
    Cohomology (twistingSheaf (MvPolynomial.homogeneousSubmodule ι R) m) q ≃ₗ[R]
      Cohomology (twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M) m) q := by
  let polynomialGrading := MvPolynomial.homogeneousSubmodule ι R
  let symmetricGrading := TauCeti.SymmetricAlgebra.homogeneousSubmodule R M
  let e : Proj polynomialGrading ≅ Proj symmetricGrading := b.polynomialProjIso
  let : e.hom.IsOver (Spec (.of R)) := ⟨by
    rw [hOver, TauCeti.SymmetricAlgebra.over_eq_projToSpec]
    exact b.polynomialProjIso_hom_over⟩
  exact e.hom.cohomologyBaseLinearEquivOfPullbackIso R
    (b.polynomialProjIsoPullbackTwistingSheafIso m) q

end Module.Basis
