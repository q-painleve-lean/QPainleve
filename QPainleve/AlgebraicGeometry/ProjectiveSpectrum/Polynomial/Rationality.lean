/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.AffineSpace.Dimension
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Integral
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Projective-space models for rational schemes

A standard coordinate open of projective space is a dense copy of affine space over an
integral domain. Over a field, a scheme of dimension `d` locally of finite type is rational
exactly when it is birational over that field to projective `d`-space. The comparison works
with both the polynomial and the symmetric-algebra presentations of projective space.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Proj

variable {R : Type u} [CommRing R] {d : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R

variable (R d) in
/-- Affine and projective space of dimension `d` over a domain are birational over the
base, via a standard coordinate open. -/
theorem birationalOver_affineSpace [IsDomain R] :
    Scheme.BirationalOver (toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R))
      (𝔸(ULift.{u} (Fin d); Spec (.of R)) ↘ _) := by
  have := isIntegral_polynomialProj (R := R) (σ := Fin (d + 1))
  let i : Fin (d + 1) := 0
  let e := basicOpenIsoAffineSpace (R := R) i
  exact ((e.inv ≫ (basicOpen 𝒜 (MvPolynomial.X i)).ι).birationalOver _ _
    ((Category.assoc _ _ _).trans (basicOpenIsoAffineSpace_inv_toSpecCoeff i))).symm

end Proj

namespace Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {d : ℕ}

variable [LocallyOfFiniteType f] in
/-- For a scheme of dimension `d` locally of finite type over a field, rationality is
equivalent to birationality over the field with polynomial projective `d`-space. -/
theorem isRationalOver_iff_birationalOver_projectiveSpace (hd : topologicalKrullDim X = d) :
    IsRationalOver f ↔ BirationalOver f
      (Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)) := by
  rw [isRationalOver_iff_birationalOver_affineSpace f hd]
  exact ⟨fun h ↦ h.trans (Proj.birationalOver_affineSpace k d).symm,
    fun h ↦ h.trans (Proj.birationalOver_affineSpace k d)⟩

variable [LocallyOfFiniteType f] in
/-- The same rationality criterion for the projective spectrum of a symmetric algebra,
with the coefficient map and basis used to compute its twisting classes. -/
theorem isRationalOver_iff_birationalOver_symmetricAlgebra {M : Type u}
    [AddCommMonoid M] [Module k M] (b : Module.Basis (Fin (d + 1)) k M)
    (hd : topologicalKrullDim X = d) :
    IsRationalOver f ↔ BirationalOver f (TauCeti.SymmetricAlgebra.projToSpec k M) := by
  rw [isRationalOver_iff_birationalOver_projectiveSpace f hd]
  have h := b.polynomialProjIso.hom.birationalOver _ _ b.polynomialProjIso_hom_over
  exact ⟨fun hf ↦ hf.trans h, fun hf ↦ hf.trans h.symm⟩

/-- A nonempty scheme smooth of relative dimension `d` over a field is rational exactly when
it is birational over the field to the projective spectrum on a basis of size `d + 1`. -/
theorem isRationalOver_iff_birationalOver_symmetricAlgebra_of_smoothOfRelativeDimension
    {M : Type u} [AddCommMonoid M] [Module k M] (b : Module.Basis (Fin (d + 1)) k M)
    [Nonempty X] [SmoothOfRelativeDimension d f] :
    IsRationalOver f ↔ BirationalOver f (TauCeti.SymmetricAlgebra.projToSpec k M) := by
  have := SmoothOfRelativeDimension.smooth d f
  exact isRationalOver_iff_birationalOver_symmetricAlgebra f b
    (TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension f)

end Scheme

end AlgebraicGeometry
