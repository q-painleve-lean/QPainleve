/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral

/-!
# Integrality of polynomial projective spectra

Over a domain a homogeneous variable witnesses that the irrelevant ideal is nonzero,
so Tau Ceti's `Proj.isIntegral_of_isDomain` applies for any nonempty coordinate type.
-/

public section

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial projective space over a domain with at least one coordinate is integral. -/
theorem isIntegral_polynomialProj {R σ : Type*} [CommRing R] [IsDomain R] [Nonempty σ] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule σ R)) := by
  apply isIntegral_of_isDomain
  intro h
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem
    (MvPolynomial.homogeneousSubmodule σ R) one_pos
    ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i))
  rw [h, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at hm
  exact MvPolynomial.X_ne_zero _ hm

end AlgebraicGeometry.Proj
