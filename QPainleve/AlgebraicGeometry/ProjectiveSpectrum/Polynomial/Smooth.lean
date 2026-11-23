/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart

/-!
# Smoothness of projective space

Projective `d`-space is smooth of relative dimension `d` over its coefficient ring.
The coordinate-chart comparison extends Tau Ceti's argument for
`TauCeti.AlgebraicGeometry.projectiveLine.smoothOfRelativeDimension` to all dimensions.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Proj

universe u

variable (R : Type u) [CommRing R] (d : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R

/-- Polynomial projective `d`-space is smooth of relative dimension `d` over `R`. -/
instance smoothOfRelativeDimension_toSpecCoeff :
    SmoothOfRelativeDimension d (toSpecCoeff 𝒜) := by
  let ι (i : Fin (d + 1)) := awayι 𝒜 (MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i)) one_pos
  let U : (Proj 𝒜).OpenCover := Scheme.Cover.mkOfCovers (Fin (d + 1)) _ ι fun x ↦ by
    have hcover := iSup_basicOpen_eq_top 𝒜 MvPolynomial.X
      (MvPolynomial.irrelevant_eq_span_X _ _).le
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
    have hr : (ι i).opensRange = basicOpen 𝒜 (MvPolynomial.X i) := opensRange_awayι _ _ _ one_pos
    rw [← hr] at hi
    obtain ⟨y, rfl⟩ := hi
    exact ⟨i, y, rfl⟩
  have (i : U.I₀) : IsAffine (U.X i) := inferInstanceAs (IsAffine (Spec _))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension d) U
  intro i
  apply (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)).mp
  have hi : SmoothOfRelativeDimension d (ι i ≫ toSpecCoeff 𝒜) := by
    have h := Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R (Fin d)
    rw [Nat.card_fin] at h
    have := Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv d
      (awayCoordinateAlgEquiv (k := R) i).symm
    dsimp only [ι]
    rw [awayι_toSpecCoeff, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr inferInstance)
  exact hi

end AlgebraicGeometry.Proj

namespace Module.Basis

universe u

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M] {d : ℕ}

/-- A basis of size `d + 1` presents the projective spectrum of the symmetric algebra
as a smooth scheme of relative dimension `d` over the coefficient ring. -/
theorem smoothOfRelativeDimension_projToSpec (b : Basis (Fin (d + 1)) R M) :
    SmoothOfRelativeDimension d (TauCeti.SymmetricAlgebra.projToSpec R M) := by
  have hs : SmoothOfRelativeDimension (0 + d)
      (b.polynomialProjIso.inv ≫ Proj.toSpecCoeff
        (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R)) := inferInstance
  rwa [← b.polynomialProjIso_hom_over, Iso.inv_hom_id_assoc, Nat.zero_add] at hs

end Module.Basis

namespace TauCeti.SymmetricAlgebra

/-- The projective spectrum of the standard free module of rank `d + 1`
is smooth of relative dimension `d` over its coefficient ring. -/
instance smoothOfRelativeDimension_over_proj_pi (R : Type u) [CommRing R] (d : ℕ) :
    SmoothOfRelativeDimension d
      (Proj (homogeneousSubmodule R (Fin (d + 1) → R)) ↘ Spec (.of R)) := by
  rw [over_eq_projToSpec]
  exact (Pi.basisFun R (Fin (d + 1))).smoothOfRelativeDimension_projToSpec

end TauCeti.SymmetricAlgebra
