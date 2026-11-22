/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.MonoidAlgebra.Smooth
public import TauCeti.Geometry.Toric.Algebraic.AffineScheme
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Regular

import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Algebraic coordinates of a regular toric chart

The primitive rays of a regular cone extend to a basis of the lattice. The corresponding
affine chart has one polynomial coordinate for each ray and one Laurent coordinate for each
remaining basis vector. The coordinate ring is standard smooth of relative dimension the rank
of the lattice.

The construction uses Tau Ceti's `regularDualSemigroupEquiv` and Mathlib's
`AddMonoidAlgebra.curryAlgEquiv`. See Fulton, *Introduction to Toric Varieties*, §2.1.
-/

public noncomputable section

open Algebra

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

section Coordinates

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

/-- In a basis extending the primitive rays, the affine chart is polynomial in the ray
variables over the Laurent algebra of the complementary variables. -/
def affineCoordinateRingEquivMvPolynomial :
    affineCoordinateRing hi σ ≃ₐ[ℂ] MvPolynomial (ToricRay σ) (AddMonoidAlgebra ℂ (ι →₀ ℤ)) :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup hi σ)).symm.trans <|
    (AddMonoidAlgebra.domCongr ℂ ℂ (regularDualSemigroupEquiv hi hσ hb)).trans
      (AddMonoidAlgebra.curryAlgEquiv ℂ)

/-- A character monomial has polynomial exponents on the rays and Laurent exponents on the
complement. -/
@[simp]
theorem affineCoordinateRingEquivMvPolynomial_single (m : dualSemigroup hi σ) (a : ℂ) :
    affineCoordinateRingEquivMvPolynomial hi hσ hb
      (MonoidAlgebra.single (Multiplicative.ofAdd m) a) =
    MvPolynomial.monomial (regularDualSemigroupEquiv hi hσ hb m).1
      (AddMonoidAlgebra.single (regularDualSemigroupEquiv hi hσ hb m).2 a) := by
  simp only [affineCoordinateRingEquivMvPolynomial, AlgEquiv.trans_apply,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_symm_single,
    AddMonoidAlgebra.domCongr_single, MvPolynomial.monomial]
  exact AddMonoidAlgebra.curryAlgEquiv_single (R := ℂ) _ _ _

end Coordinates

/-- The coordinate algebra of a regular cone is standard smooth over `ℂ`, of relative
dimension the rank of the lattice. -/
theorem IsRegularCone.isStandardSmoothOfRelativeDimension_affineCoordinateRing
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i) :
    IsStandardSmoothOfRelativeDimension (Module.finrank ℤ N) ℂ (affineCoordinateRing hi σ) := by
  classical
  obtain ⟨l, b, hb⟩ := hσ.exists_basis_sum
  let := ToricRay.finite_of_fg hσ.fg
  let := Fintype.ofFinite (ToricRay σ)
  let R := AddMonoidAlgebra ℂ (Fin l →₀ ℤ)
  let S := MvPolynomial (ToricRay σ) R
  have hdim : Module.finrank ℤ N = Nat.card (ToricRay σ) + l := by
    simpa [Nat.card_sum] using Module.finrank_eq_card_basis b
  have : IsStandardSmoothOfRelativeDimension l ℂ R := by
    simpa [R] using AddMonoidAlgebra.isStandardSmoothOfRelativeDimension_finsupp_int ℂ (Fin l)
  have : IsStandardSmoothOfRelativeDimension (Nat.card (ToricRay σ)) R S :=
    IsStandardSmoothOfRelativeDimension.mvPolynomial R (ToricRay σ)
  have : IsStandardSmoothOfRelativeDimension (Nat.card (ToricRay σ) + l) ℂ S :=
    IsStandardSmoothOfRelativeDimension.trans (n := l) (m := Nat.card (ToricRay σ)) ℂ R S
  rw [hdim]
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv _
    (affineCoordinateRingEquivMvPolynomial hi hσ.toIsToricCone hb).symm

end TauCeti.Toric
