/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# Polynomial and symmetric-algebra presentations of projective space

A basis identifies the two projective spectra over the coefficient ring and identifies their
twisting sheaves. The comparison uses Tau Ceti's degreewise comparison for
`SymmetricAlgebra.equivMvPolynomial`.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory

universe u v

namespace Module.Basis

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type (max u v)} [CommRing R] [AddCommMonoid M] [Module R M] {ι : Type v}

local notation "𝒮" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R M
local notation "𝒫" => MvPolynomial.homogeneousSubmodule ι R

private def toPolynomialGradedHom (b : Basis ι R M) : 𝒮 →+*ᵍ 𝒫 where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem {i x} hx := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b i x).mpr hx)

private def fromPolynomialGradedHom (b : Basis ι R M) : 𝒫 →+*ᵍ 𝒮 where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
  map_mem {i x} hx := (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b i _).mp
    (by
      have h : SymmetricAlgebra.equivMvPolynomial b
          ((SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom x) = x :=
        (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x
      rw [h]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp hx)

private theorem toPolynomialGradedHom_surjective (b : Basis ι R M) :
    Function.Surjective (toPolynomialGradedHom b) :=
  (SymmetricAlgebra.equivMvPolynomial b).surjective

/-- The isomorphism from polynomial projective space to the projective spectrum of the
symmetric algebra obtained by choosing a basis of the module. -/
def polynomialProjIso (b : Basis ι R M) : Proj 𝒫 ≅ Proj 𝒮 :=
  mapIso (toPolynomialGradedHom b) (fromPolynomialGradedHom b)
    (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply
    (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply

private theorem polynomialProjIso_hom (b : Basis ι R M) :
    b.polynomialProjIso.hom = map (toPolynomialGradedHom b)
      (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (toPolynomialGradedHom_surjective b)) :=
  mapIso_hom _ _ _ _

/-- The basis comparison preserves the projective structure morphisms. -/
@[reassoc (attr := simp)]
theorem polynomialProjIso_hom_over (b : Basis ι R M) :
    b.polynomialProjIso.hom ≫ TauCeti.SymmetricAlgebra.projToSpec R M = toSpecCoeff 𝒫 := by
  rw [polynomialProjIso_hom, TauCeti.SymmetricAlgebra.projToSpec_def, ← toSpecCoeff_def]
  apply map_toSpecCoeff
  intro r
  apply Subtype.ext
  rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
    SetLike.GradeZero.coe_algebraMap]
  exact (SymmetricAlgebra.equivMvPolynomial b).commutes r

/-- The basis comparison pulls the symmetric-algebra twist back to the same polynomial twist. -/
def polynomialProjIsoPullbackTwistingSheafIso (b : Basis ι R M) (m : ℤ) :
    (Scheme.Modules.pullback b.polynomialProjIso.hom).obj (twistingSheaf 𝒮 m) ≅
      twistingSheaf 𝒫 m := by
  rw [polynomialProjIso_hom]
  exact asIso (pullbackTwistingSheafMap (toPolynomialGradedHom b)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (toPolynomialGradedHom_surjective b)) m)

end Module.Basis
