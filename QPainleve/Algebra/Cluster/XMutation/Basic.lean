/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import QPainleve.Algebra.Cluster.XMutation.Chart
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
import TauCeti.RingTheory.Localization.Away.FractionRing

/-!
# Cluster X mutation on the rational function field

A column of an integer exchange matrix determines an algebra automorphism of the
fraction field of the Laurent coordinate ring. Replacing the column by its negative
gives the inverse. The construction first inverts `1 + Xₚ` in the Laurent ring,
where mutation in direction `p` is already an isomorphism.

The coordinate formula is that of Fock and Goncharov, *Cluster ensembles,
quantization and the dilogarithm*, §1.2.2 (7) and §1.2.4 (13).
Tau Ceti's `Localization.Away.isFractionRing` passes from the open chart to the field.
-/

public noncomputable section

namespace QPainleve.Cluster

open TauCeti LaurentRing

variable (k : Type*) [CommRing k] {ι : Type*}

local notation "Laurent" => LaurentRing k ι
local notation "Functions" => FractionRing (LaurentRing k ι)

/-- The independent Laurent coordinate corresponding to the label `i`. -/
def xCoordinate (i : ι) : Functions :=
  algebraMap Laurent Functions (X i)

/-- The coordinate is the image of the unit-exponent monomial in the Laurent ring. -/
theorem xCoordinate_def (i : ι) :
    xCoordinate k i =
      algebraMap Laurent Functions (AddMonoidAlgebra.single (Finsupp.single i 1) 1) := by
  rw [xCoordinate, X_def]

variable [IsDomain k]

/-- Each coordinate is nonzero in the field of independent X coordinates. -/
@[simp] theorem xCoordinate_ne_zero (i : ι) : xCoordinate k i ≠ 0 := by
  rw [xCoordinate_def, ← map_zero (algebraMap Laurent Functions)]
  exact (IsFractionRing.injective Laurent Functions).ne
    (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)

private theorem binomial_ne_zero (p : ι) : 1 + (X p : Laurent) ≠ 0 := by
  classical
  have hp : Finsupp.single p (1 : ℤ) ≠ 0 := by simp
  intro h
  have hCoeff := congrArg (fun f : Laurent ↦ f.coeff 0) h
  simp [X_def, AddMonoidAlgebra.coeff_add, hp] at hCoeff

/-- The mutation binomial is nonzero in the field of independent X coordinates. -/
@[simp] theorem one_add_xCoordinate_ne_zero (i : ι) : 1 + xCoordinate k i ≠ 0 := by
  simpa only [xCoordinate, map_add, map_one, map_zero] using
    (IsFractionRing.injective Laurent Functions).ne (binomial_ne_zero k i)

variable (p : ι)

local notation "Chart" => XMutationChart k p

private noncomputable instance chartAlgebra : Algebra Chart Functions :=
  Localization.Away.algebraOfIsFractionRing Functions (binomial_ne_zero k p)

private instance chartLaurentTower : IsScalarTower Laurent Chart Functions :=
  Localization.Away.isScalarTower_of_isFractionRing Functions (binomial_ne_zero k p)

private instance chartTower : IsScalarTower k Chart Functions :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k Laurent Chart, ← RingHom.comp_apply,
      ← IsScalarTower.algebraMap_eq Laurent Chart Functions, ← IsScalarTower.algebraMap_apply]

private instance chartFractionRing : IsFractionRing Chart Functions :=
  Localization.Away.isFractionRing Functions (binomial_ne_zero k p)

/-- The canonical inclusion of the open mutation chart into the X function field. -/
def xMutationChartToFunctionField : Chart →ₐ[k] Functions :=
  IsScalarTower.toAlgHom k Chart Functions

/-- The chart inclusion extends the Laurent ring inclusion. -/
@[simp]
theorem xMutationChartToFunctionField_algebraMap (x : Laurent) :
    xMutationChartToFunctionField k p (algebraMap Laurent Chart x) =
      algebraMap Laurent Functions x :=
  (IsScalarTower.algebraMap_apply Laurent Chart Functions x).symm

/-- The localization embeds into the function field. -/
theorem xMutationChartToFunctionField_injective :
    Function.Injective (xMutationChartToFunctionField k p) :=
  IsFractionRing.injective Chart Functions

/-- Pullback on the field of independent cluster X coordinates for mutation at `p`,
with `a i` the `(i,p)` entry of the exchange matrix. -/
def xMutation (a : ι → ℤ) : Functions ≃ₐ[k] Functions :=
  IsFractionRing.algEquivOfAlgEquiv (xMutationChartEquiv k p a)

/-- The field pullback extends the open chart automorphism. -/
@[simp]
theorem xMutation_xMutationChartToFunctionField (a : ι → ℤ) (x : Chart) :
    xMutation k p a (xMutationChartToFunctionField k p x) =
      xMutationChartToFunctionField k p (xMutationChartEquiv k p a x) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

private theorem xMutationChartToFunctionField_unitX (i : ι) :
    xMutationChartToFunctionField k p (xMutationChartUnitX k p i : Chart) = xCoordinate k i := by
  simp [xCoordinate]

private theorem xMutationChartToFunctionField_binomial :
    xMutationChartToFunctionField k p (xMutationChartBinomial k p : Chart) =
      1 + xCoordinate k p := by
  simp [xCoordinate]

/-- The mutated coordinate pulls back to its reciprocal. -/
@[simp] theorem xMutation_apply_self (a : ι → ℤ) :
    xMutation k p a (xCoordinate k p) = (xCoordinate k p)⁻¹ := by
  have h := congrArg (Units.map (xMutationChartToFunctionField k p : Chart →* Functions))
    (map_xMutationChartUnitX_self k p a)
  rw [map_inv] at h
  simpa only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
    ← xMutation_xMutationChartToFunctionField, xMutationChartToFunctionField_unitX] using
    congrArg Units.val h

/-- The pullback of an X coordinate away from the mutation direction. -/
theorem xMutation_apply_of_ne (a : ι → ℤ) {i : ι} (hi : i ≠ p) :
    xMutation k p a (xCoordinate k i) =
      xCoordinate k i * (xCoordinate k p) ^ max (a i) 0 * (1 + xCoordinate k p) ^ (-a i) := by
  have h := congrArg (Units.map (xMutationChartToFunctionField k p : Chart →* Functions))
    (map_xMutationChartUnitX_of_ne k p a hi)
  simp only [map_mul, map_zpow] at h
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_ofClass,
    ← xMutation_xMutationChartToFunctionField, xMutationChartToFunctionField_unitX,
    xMutationChartToFunctionField_binomial] using congrArg Units.val h

/-- Reversing the mutation negates the exchange column. -/
@[simp] theorem xMutation_symm (a : ι → ℤ) :
    (xMutation k p a).symm = xMutation k p (-a) := by
  simp [xMutation, IsFractionRing.algEquivOfAlgEquiv_symm]

/-- Pullback along the return mutation is the inverse of pullback along the original mutation. -/
theorem xMutation_symm_matrixMutation [DecidableEq ι] (B : Matrix ι ι ℤ) :
    (xMutation k p (fun i ↦ B i p)).symm =
      xMutation k p (fun i ↦ TauCeti.matrixMutation (Function.Embedding.refl ι) B p i p) := by
  simp [TauCeti.matrixMutation_apply_col, ← Pi.neg_def]

end QPainleve.Cluster
