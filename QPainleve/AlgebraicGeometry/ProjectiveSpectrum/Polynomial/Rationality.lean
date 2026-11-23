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
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral

/-!
# Projective-space models for rational schemes

A standard coordinate open of projective space is a dense copy of affine space over an
integral domain. Over a field, a scheme of dimension `d` locally of finite type is rational
exactly when it is birational over that field to projective `d`-space. The comparison works
with both the polynomial and the symmetric-algebra presentations of projective space.

The chart comparison uses dehomogenization and Mathlib's `AffineSpace.SpecIso`. Its structure
map is given by Tau Ceti's `Proj.awayι_toSpecCoeff`.
-/

public noncomputable section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Proj

variable {R : Type u} [CommRing R] {d : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R

private def affineSpaceChartIso (i : Fin (d + 1)) :
    𝔸(ULift.{u} (Fin d); Spec (.of R)) ≅ Spec (.of (Away 𝒜 (MvPolynomial.X i))) :=
  AffineSpace.SpecIso _ _ ≪≫ Scheme.Spec.mapIso
    ((awayCoordinateAlgEquiv (k := R) i).trans
      (MvPolynomial.renameEquiv R Equiv.ulift.symm)).toRingEquiv.toCommRingCatIso.op

/-- A standard coordinate open of polynomial projective space is affine space.
The affine variable indexed by `j` corresponds to the ratio `Xᵢ.succAbove j / Xᵢ`. -/
def basicOpenIsoAffineSpace (i : Fin (d + 1)) :
    (basicOpen 𝒜 (MvPolynomial.X i)).toScheme ≅ 𝔸(ULift.{u} (Fin d); Spec (.of R)) :=
  basicOpenIsoSpec 𝒜 _ ((MvPolynomial.mem_homogeneousSubmodule ..).mpr
    (MvPolynomial.isHomogeneous_X R i)) one_pos ≪≫ (affineSpaceChartIso i).symm

/-- The affine-space inclusion into the coordinate open lies over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem basicOpenIsoAffineSpace_inv_toSpecCoeff (i : Fin (d + 1)) :
    (basicOpenIsoAffineSpace (R := R) i).inv ≫ (basicOpen 𝒜 (MvPolynomial.X i)).ι ≫
      toSpecCoeff 𝒜 = 𝔸(ULift.{u} (Fin d); Spec (.of R)) ↘ Spec (.of R) := by
  rw [basicOpenIsoAffineSpace, Iso.trans_inv, Category.assoc, Iso.symm_inv,
    basicOpenIsoSpec_inv_ι_assoc, awayι_toSpecCoeff, affineSpaceChartIso, Iso.trans_hom,
    Category.assoc, ← Iso.eq_inv_comp, AffineSpace.SpecIso_inv_over]
  rw [Scheme.Spec.mapIso_hom, Scheme.Spec_map, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ((awayCoordinateAlgEquiv (k := R) i).trans
    (MvPolynomial.renameEquiv R Equiv.ulift.symm)).commutes r

variable (R d) in
/-- Affine and projective space of dimension `d` over a domain are birational over the
base, via a standard coordinate open. -/
theorem birationalOver_affineSpace [IsDomain R] :
    Scheme.BirationalOver (toSpecCoeff (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) R))
      (𝔸(ULift.{u} (Fin d); Spec (.of R)) ↘ _) := by
  have h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥ := by
    intro he
    have hx := HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos
      ((MvPolynomial.mem_homogeneousSubmodule ..).mpr
        (MvPolynomial.isHomogeneous_X R (0 : Fin (d + 1))))
    have hx' : MvPolynomial.X 0 ∈ (⊥ : HomogeneousIdeal 𝒜).toIdeal := he ▸ hx
    exact MvPolynomial.X_ne_zero _ (by simpa only [HomogeneousIdeal.toIdeal_bot,
      Ideal.mem_bot] using hx')
  have : IsIntegral (Proj 𝒜) := isIntegral_of_isDomain 𝒜 h
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
