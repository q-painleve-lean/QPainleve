/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change of polynomial projective space

The coefficient map on multivariate polynomial rings induces the base-change projection
on their projective spectra. The cartesian square identifies projective space over an
affine algebra with the corresponding product over the coefficient base.

The comparison uses Mathlib's `MvPolynomial.algebraTensorAlgEquiv` and Tau Ceti's
`Proj.isPullback_map_of_isBaseChange`.
-/

public noncomputable section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" => homogeneousSubmodule ι R
local notation "ℬ" => homogeneousSubmodule ι S

private def polynomialGradedMap : 𝒜 →+*ᵍ ℬ :=
  ⟨MvPolynomial.map (algebraMap R S), fun hp ↦
    ((mem_homogeneousSubmodule _ _).mp hp).map (algebraMap R S)⟩

private theorem polynomialGradedMap_algebraMap (r : R) :
    polynomialGradedMap (S := S) ι (algebraMap R (MvPolynomial ι R) r) =
      algebraMap R (MvPolynomial ι S) r := by
  rw [IsScalarTower.algebraMap_apply R S (MvPolynomial ι S)]
  -- The underlying graded map applies the coefficient homomorphism.
  change MvPolynomial.map (algebraMap R S) (C r) = C (algebraMap R S r)
  exact MvPolynomial.map_C _ _

private theorem polynomialGradedMap_isBaseChange :
    IsBaseChange S
      (AlgHom.mk (R := R) (polynomialGradedMap (S := S) ι).toRingHom
        (polynomialGradedMap_algebraMap (S := S) ι)).toLinearMap :=
  IsBaseChange.of_equiv (MvPolynomial.algebraTensorAlgEquiv R S).toLinearEquiv
    (by
      intro p
      -- Read the two linear maps on the pure tensor and on the input polynomial.
      change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] p) =
        MvPolynomial.map (algebraMap R S) p
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul])

/-- The projection from polynomial projective space after extending the coefficient ring. -/
def polynomialBaseChangeProjection : Proj ℬ ⟶ Proj 𝒜 :=
  Proj.map (polynomialGradedMap (R := R) (S := S) ι)
    (HomogeneousIdeal.irrelevant_le_map_of_isBaseChange 𝒜 (polynomialGradedMap (R := R) (S := S) ι)
      (polynomialGradedMap_algebraMap (S := S) ι)
      (polynomialGradedMap_isBaseChange (R := R) (S := S) ι))

/-- The square exhibiting polynomial projective space as a base change. -/
theorem isPullback_polynomialBaseChangeProjection :
    IsPullback (polynomialBaseChangeProjection (R := R) (S := S) ι) (Proj.toSpecCoeff ℬ)
      (Proj.toSpecCoeff 𝒜) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  Proj.isPullback_map_of_isBaseChange 𝒜 (polynomialGradedMap (R := R) (S := S) ι)
    (polynomialGradedMap_algebraMap (S := S) ι)
      (polynomialGradedMap_isBaseChange (R := R) (S := S) ι)

/-- The coefficient map after extension is the original coefficient morphism followed by
the morphism of affine bases. -/
@[reassoc (attr := simp)]
theorem polynomialBaseChangeProjection_toSpecCoeff :
    polynomialBaseChangeProjection (R := R) (S := S) ι ≫ Proj.toSpecCoeff 𝒜 =
      Proj.toSpecCoeff ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (isPullback_polynomialBaseChangeProjection ι).w

/-- The projection preserves the index of each projective coordinate open. -/
@[simp]
theorem polynomialBaseChangeProjection_preimage_basicOpen (i : ι) :
    polynomialBaseChangeProjection (R := R) (S := S) ι ⁻¹ᵁ Proj.basicOpen 𝒜 (.X i) =
      Proj.basicOpen ℬ (.X i) := by
  rw [polynomialBaseChangeProjection, Proj.map_preimage_basicOpen]
  exact congrArg (Proj.basicOpen ℬ) (MvPolynomial.map_X _ _)

/-- The coefficient projection sends a homogeneous-coordinate morphism to the same
coordinates read over the smaller ring. -/
theorem fromOfGlobalSections_polynomialBaseChangeProjection
    {T : Scheme.{u}} (b : S →+* Γ(T, ⊤)) (s : ι → Γ(T, ⊤))
    (hs : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map (eval₂Hom b s) = ⊤) :
    ∃ ht : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (eval₂Hom (b.comp (algebraMap R S)) s) = ⊤,
      fromOfGlobalSections ℬ (eval₂Hom b s) hs ≫
        polynomialBaseChangeProjection (R := R) (S := S) ι =
      fromOfGlobalSections 𝒜 (eval₂Hom (b.comp (algebraMap R S)) s) ht := by
  rw [polynomialBaseChangeProjection, fromOfGlobalSections_map]
  have he : (eval₂Hom b s).comp (polynomialGradedMap (R := R) (S := S) ι).toRingHom =
      eval₂Hom (b.comp (algebraMap R S)) s := by
    apply MvPolynomial.ringHom_ext
    · intro r
      -- The graded map acts coefficientwise, including on the constant polynomials.
      change eval₂Hom b s (MvPolynomial.map (algebraMap R S) (C r)) = _
      simp
    · intro i
      -- The graded map fixes each variable.
      change eval₂Hom b s (MvPolynomial.map (algebraMap R S) (X i)) = _
      simp
  have ht : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
      (eval₂Hom (b.comp (algebraMap R S)) s) = ⊤ := by
    rw [irrelevant_eq_span_X, Ideal.map_span, ← Set.range_comp] at hs ⊢
    simpa only [Function.comp_def, eval₂Hom_X'] using hs
  exact ⟨ht, by congr 1⟩

end AlgebraicGeometry.Proj
