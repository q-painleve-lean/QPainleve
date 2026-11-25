/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap

/-!
# Swapping the coordinates of the projective line

Exchanging the two homogeneous coordinates exchanges the polynomial charts,
preserving the affine coordinate when it is read in the exchanged chart.
As for Tau Ceti's `projectiveLine.scalingBy`, the construction uses the
projective isomorphism induced by a linear equivalence.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable (R : Type u) [CommRing R]

local notation "e" => LinearEquiv.funCongrLeft R R (Fin.revPerm (n := 2))

/-- The projective linear isomorphism `[x₀ : x₁] ↦ [x₁ : x₀]`. -/
def coordinateSwap : projectiveLine R ≅ projectiveLine R :=
  Proj.symmetricAlgebraMapIso R e

/-- The coordinate swap is its own inverse. -/
@[simp]
theorem coordinateSwap_symm : (coordinateSwap R).symm = coordinateSwap R := by
  rw [coordinateSwap, ← Proj.symmetricAlgebraMapIso_symm, LinearEquiv.funCongrLeft_symm,
    Fin.revPerm_symm]

/-- Applying the coordinate swap twice restores the original homogeneous coordinates. -/
@[reassoc (attr := simp)]
theorem coordinateSwap_hom_comp_hom :
    (coordinateSwap R).hom ≫ (coordinateSwap R).hom = 𝟙 (projectiveLine R) := by
  have hinv : (coordinateSwap R).inv = (coordinateSwap R).hom :=
    congrArg Iso.hom (coordinateSwap_symm R)
  simpa only [hinv] using (coordinateSwap R).hom_inv_id

/-- Swapping the coordinates preserves the structure map to the coefficient scheme. -/
instance isOver_coordinateSwap_hom :
    (coordinateSwap R).hom.IsOver (Spec (.of R)) where
  comp_over := by
    simpa only [coordinateSwap, SymmetricAlgebra.over_eq_projToSpec] using
      Proj.symmetricAlgebraMapIso_hom_projToSpec R e

private theorem pointCoordinates_comp_swap {A : Type u} [CommSemiring A]
    (f : R →+* A) (j : Fin 2) (a : A) :
    (pointCoordinates R f j a).comp
        (_root_.SymmetricAlgebra.gradedMap R (e).toLinearMap).toRingHom =
      pointCoordinates R f j.rev a := by
  apply _root_.SymmetricAlgebra.ringHom_ext
  · ext r
    simp
  · intro v
    rw [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
      _root_.SymmetricAlgebra.gradedMap_apply, _root_.SymmetricAlgebra.map_apply_ι,
      ι_eq_smul_coord_add_smul_coord R j, ι_eq_smul_coord_add_smul_coord R j.rev]
    have h := pointCoordinates_coord_rev R f j.rev a
    rw [Fin.rev_rev] at h
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Algebra.smul_def, h]

/-- Swapping the homogeneous coordinates carries a polynomial point to the other
chart with the same normalized coordinate. -/
@[reassoc (attr := simp)]
theorem polynomialPoint_comp_coordinateSwap {A : Type u} [CommRing A]
    (f : R →+* A) (j : Fin 2) (a : A) :
    polynomialPoint R f j a ≫ (coordinateSwap R).hom = polynomialPoint R f j.rev a := by
  rw [coordinateSwap, Proj.symmetricAlgebraMapIso_hom, polynomialPoint_eq_fromGlobalSections,
    Proj.fromOfGlobalSections_map]
  simp only [RingHom.comp_assoc, pointCoordinates_comp_swap]
  exact (polynomialPoint_eq_fromGlobalSections R f j.rev a).symm

/-- Swapping the homogeneous coordinates exchanges the two polynomial charts. -/
@[reassoc (attr := simp)]
theorem polynomialChartι_comp_coordinateSwap (j : Fin 2) :
    polynomialChartι R j ≫ (coordinateSwap R).hom = polynomialChartι R j.rev := by
  have hid : eval₂RingHom (C : R →+* R[X]) X = RingHom.id _ :=
    RingHom.ext fun p ↦ eval₂_C_X
  simpa only [polynomialPoint_def, Category.assoc, hid,
    CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using
      polynomialPoint_comp_coordinateSwap R C j X

end TauCeti.AlgebraicGeometry.projectiveLine
