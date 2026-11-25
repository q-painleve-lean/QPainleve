/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

/-!
# Transition functions for twists on the projective line

On the intersection of the two standard affine charts, the coordinate
`X₁ / X₀` is a unit. Its integral powers compare the two standard generators
of each twisting sheaf. These transition functions also determine the
projective coordinates of a projectivized sum of twists.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Opposite
open HomogeneousLocalization

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "P" => projectiveLine R
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)
local notation "U[" i "]" => Proj.basicOpen 𝒜 (coord R i)

/-- On any common subopen of the two charts of the projective line,
`X₁ / X₀` is a unit with inverse `X₀ / X₁`. -/
def affineCoordinateUnit {V : (P).Opens} (h₀ : V ≤ U[0]) (h₁ : V ≤ U[1]) :
    Γ(P, V)ˣ where
  val := (P).presheaf.map (homOfLE h₀).op (affineCoordinate R 0)
  inv := (P).presheaf.map (homOfLE h₁).op (affineCoordinate R 1)
  val_inv := affineCoordinate_res_mul R V h₀ h₁
  inv_val := (mul_comm _ _).trans (affineCoordinate_res_mul R V h₀ h₁)

/-- The overlap unit is the restriction of the first affine coordinate. -/
@[simp]
theorem coe_affineCoordinateUnit {V : (P).Opens} (h₀ : V ≤ U[0]) (h₁ : V ≤ U[1]) :
    ↑(affineCoordinateUnit R h₀ h₁) =
      (P).presheaf.map (homOfLE h₀).op (affineCoordinate R 0) :=
  (rfl)

/-- The inverse overlap unit is the restriction of the second affine coordinate. -/
@[simp]
theorem coe_affineCoordinateUnit_inv {V : (P).Opens} (h₀ : V ≤ U[0]) (h₁ : V ≤ U[1]) :
    ↑((affineCoordinateUnit R h₀ h₁)⁻¹) =
      (P).presheaf.map (homOfLE h₁).op (affineCoordinate R 1) :=
  (rfl)

/-- The standard generator of `𝒪(n)` on the second chart is the standard generator
on the first chart multiplied by the `n`th power of `X₁/X₀` on their overlap. -/
theorem chartGenerator_one_eq_smul_chartGenerator_zero (n : ℤ) {V : (P).Opens}
    (h₀ : V ≤ U[0]) (h₁ : V ≤ U[1]) :
    twistingSheaf.chartGenerator n (coord R 1) (coord_mem R 1) V h₁ =
      (↑(affineCoordinateUnit R h₀ h₁ ^ n) : Γ(P, V)) •
        twistingSheaf.chartGenerator n (coord R 0) (coord_mem R 0) V h₀ := by
  apply twistingSheaf.ext
  intro x
  let := x.val.isPrime
  cases n with
  | ofNat m =>
    erw [twistingSheaf.smul_apply, zpow_natCast, Units.val_pow_eq_pow_val,
      coe_affineCoordinateUnit, Proj.pow_apply, val_pow, val_res_affineCoordinate]
    simp only [twistingSheaf.chartGenerator_apply, Localization.mk_pow, Localization.mk_mul]
    apply Localization.mk_eq_mk_iff.mpr
    apply Localization.r_of_eq
    simp [Fin.rev, mul_comm]
  | negSucc m =>
    erw [twistingSheaf.smul_apply, Int.negSucc_eq, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, coe_affineCoordinateUnit_inv, Proj.pow_apply,
      val_pow, val_res_affineCoordinate]
    simp only [twistingSheaf.chartGenerator_apply,
      neg_neg, Localization.mk_pow, Localization.mk_mul]
    apply Localization.mk_eq_mk_iff.mpr
    apply Localization.r_of_eq
    simp only [Int.toNat_of_nonpos (by omega : -(↑m + 1 : ℤ) ≤ 0), pow_zero, mul_one]
    rfl

end TauCeti.AlgebraicGeometry.projectiveLine
