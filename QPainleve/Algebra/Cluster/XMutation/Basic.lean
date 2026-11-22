/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Group
import TauCeti.Algebra.Group.FreeAbelianCharacter
import TauCeti.RingTheory.Localization.Away.FractionRing

/-!
# Cluster X mutation on the rational function field

A column of an integer exchange matrix determines an algebra automorphism of the
fraction field of the Laurent coordinate ring. Replacing the column by its negative
gives the inverse. The construction first inverts `1 + Xₚ` in the Laurent ring,
where mutation in direction `p` is already an isomorphism.

The coordinate formula is that of Fock and Goncharov, *Cluster ensembles,
quantization and the dilogarithm*, §1.2.2 (7) and §1.2.4 (13). The construction
uses `Localization.Away.isFractionRing` to pass from the open chart to the field.
Tau Ceti's `freeAbelianCharEquiv` extends the coordinate units to a character of the
exponent lattice and determines that character by its values on the standard generators.
-/

public noncomputable section

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι : Type*}

local notation "Laurent" => AddMonoidAlgebra k (ι →₀ ℤ)
local notation "Functions" => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

/-- The independent Laurent coordinate corresponding to the label `i`. -/
def xCoordinate (i : ι) : Functions :=
  algebraMap Laurent Functions (AddMonoidAlgebra.single (Finsupp.single i 1) 1)

/-- The coordinate is the image of the unit-exponent monomial in the Laurent ring. -/
theorem xCoordinate_def (i : ι) :
    xCoordinate k i =
      algebraMap Laurent Functions (AddMonoidAlgebra.single (Finsupp.single i 1) 1) := (rfl)

/-- Each coordinate is nonzero in the field of independent X coordinates. -/
@[simp] theorem xCoordinate_ne_zero (i : ι) : xCoordinate k i ≠ 0 := by
  rw [xCoordinate_def, ← map_zero (algebraMap Laurent Functions)]
  exact (IsFractionRing.injective Laurent Functions).ne
    (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)

private abbrev coordinate (i : ι) : Laurent :=
  AddMonoidAlgebra.single (Finsupp.single i 1) 1

private theorem binomial_ne_zero (p : ι) : 1 + coordinate k p ≠ 0 := by
  classical
  have hp : Finsupp.single p (1 : ℤ) ≠ 0 := by simp
  intro h
  have hCoeff := congrArg (fun f : Laurent ↦ f.coeff 0) h
  simp [AddMonoidAlgebra.coeff_add, hp] at hCoeff

/-- The mutation binomial is nonzero in the field of independent X coordinates. -/
@[simp] theorem one_add_xCoordinate_ne_zero (i : ι) : 1 + xCoordinate k i ≠ 0 := by
  rw [xCoordinate_def, ← map_one (algebraMap Laurent Functions), ← map_add,
    ← map_zero (algebraMap Laurent Functions)]
  exact (IsFractionRing.injective Laurent Functions).ne (binomial_ne_zero k i)

variable (p : ι)

local notation "Chart" => Localization.Away (1 + coordinate k p)

private def coordinateUnit (i : ι) : Chartˣ :=
  ((algebraMap Laurent Chart).toMonoidHom.comp
    (AddMonoidAlgebra.of k (ι →₀ ℤ))).toHomUnits
      (Multiplicative.ofAdd (Finsupp.single i 1))

private theorem coe_coordinateUnit (i : ι) :
    (coordinateUnit k p i : Chart) = algebraMap Laurent Chart (coordinate k i) := by
  simp [coordinateUnit, AddMonoidAlgebra.of_apply]

private def binomialUnit : Chartˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Chart) (1 + coordinate k p)).unit

private theorem coe_binomialUnit :
    (binomialUnit k p : Chart) = 1 + (coordinateUnit k p p : Chart) := by
  simp [binomialUnit, coe_coordinateUnit]

/-- The other binomial on the same open torus chart is `1 + Xₚ⁻¹ = Xₚ⁻¹(1 + Xₚ)`. -/
private def inverseBinomialUnit : Chartˣ :=
  (coordinateUnit k p p)⁻¹ * binomialUnit k p

private theorem coe_inverseBinomialUnit :
    (inverseBinomialUnit k p : Chart) = 1 + (↑((coordinateUnit k p p)⁻¹) : Chart) := by
  simp [inverseBinomialUnit, coe_binomialUnit, mul_add, add_comm]

private def mutatedCoordinate (a : ι → ℤ) (i : ι) : Chartˣ := by
  classical
  exact if i = p then (coordinateUnit k p p)⁻¹
    else coordinateUnit k p i * (binomialUnit k p) ^ max (-a i) 0 *
      (inverseBinomialUnit k p) ^ (-max (a i) 0)

private theorem mutatedCoordinate_self (a : ι → ℤ) :
    mutatedCoordinate k p a p = (coordinateUnit k p p)⁻¹ := by
  simp [mutatedCoordinate]

private theorem mutatedCoordinate_of_ne (a : ι → ℤ) {i : ι} (hi : i ≠ p) :
    mutatedCoordinate k p a i =
      coordinateUnit k p i * (binomialUnit k p) ^ max (-a i) 0 *
        (inverseBinomialUnit k p) ^ (-max (a i) 0) := by
  simp [mutatedCoordinate, hi]

private def mutationOnLaurent (a : ι → ℤ) : Laurent →ₐ[k] Chart :=
  AddMonoidAlgebra.lift k Chart (ι →₀ ℤ) <| (Units.coeHom Chart).comp
    (TauCeti.freeAbelianCharEquiv.symm (mutatedCoordinate k p a))

private theorem mutationOnLaurent_coordinate (a : ι → ℤ) (i : ι) :
    mutationOnLaurent k p a (coordinate k i) = (mutatedCoordinate k p a i : Chart) := by
  simp only [mutationOnLaurent, AddMonoidAlgebra.lift_single, one_smul, MonoidHom.comp_apply,
    TauCeti.freeAbelianCharEquiv_symm_apply_ofAdd_single, Units.coeHom_apply]

private def mutationOnChart (a : ι → ℤ) : Chart →ₐ[k] Chart :=
  IsLocalization.Away.liftAlgHom (1 + coordinate k p)
    (f := mutationOnLaurent k p a) (by
      simp [mutationOnLaurent_coordinate, mutatedCoordinate, ← coe_inverseBinomialUnit])

private theorem mutationOnChart_coordinate (a : ι → ℤ) (i : ι) :
    mutationOnChart k p a (coordinateUnit k p i : Chart) = (mutatedCoordinate k p a i : Chart) := by
  simp [coe_coordinateUnit, mutationOnChart, mutationOnLaurent_coordinate]

private theorem map_coordinateUnit (a : ι → ℤ) (i : ι) :
    Units.map (mutationOnChart k p a).toMonoidHom (coordinateUnit k p i) =
      mutatedCoordinate k p a i :=
  Units.ext (mutationOnChart_coordinate k p a i)

private theorem map_binomialUnit (a : ι → ℤ) :
    Units.map (mutationOnChart k p a).toMonoidHom (binomialUnit k p) =
      inverseBinomialUnit k p := by
  apply Units.ext
  calc
    _ = mutationOnChart k p a (binomialUnit k p : Chart) := Units.coe_map _ _
    _ = _ := by
      rw [coe_binomialUnit, map_add, map_one, mutationOnChart_coordinate, mutatedCoordinate_self,
        coe_inverseBinomialUnit]

private theorem map_inverseBinomialUnit (a : ι → ℤ) :
    Units.map (mutationOnChart k p a).toMonoidHom (inverseBinomialUnit k p) =
      binomialUnit k p := by
  simp only [inverseBinomialUnit, map_mul, map_inv, map_coordinateUnit, map_binomialUnit]
  simp [mutatedCoordinate_self]

private theorem map_mutatedCoordinate_neg (a : ι → ℤ) (i : ι) :
    Units.map (mutationOnChart k p a).toMonoidHom (mutatedCoordinate k p (-a) i) =
      coordinateUnit k p i := by
  by_cases hi : i = p
  · subst i
    rw [mutatedCoordinate_self, map_inv, map_coordinateUnit, mutatedCoordinate_self, inv_inv]
  · simp only [mutatedCoordinate_of_ne _ _ _ hi, Pi.neg_apply, neg_neg, map_mul, map_zpow,
      map_coordinateUnit, map_binomialUnit, map_inverseBinomialUnit]
    group

private theorem mutationOnChart_comp_neg (a : ι → ℤ) :
    (mutationOnChart k p a).comp (mutationOnChart k p (-a)) = AlgHom.id k Chart := by
  apply Localization.algHom_ext
  apply (AddMonoidAlgebra.lift k Chart (ι →₀ ℤ)).symm.injective
  apply MonoidHom.toHomUnitsMulEquiv.injective
  apply TauCeti.freeAbelianCharEquiv.injective
  funext i
  apply Units.ext
  simp only [TauCeti.freeAbelianCharEquiv_apply, MonoidHom.toHomUnitsMulEquiv_apply,
    MonoidHom.coe_toHomUnits, AddMonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.id_apply,
    toAdd_ofAdd, Algebra.algHom, IsScalarTower.toAlgHom_apply, ← coe_coordinateUnit,
    mutationOnChart_coordinate]
  exact (Units.coe_map _ _).symm.trans
    (congrArg (fun u : Chartˣ ↦ (u : Chart)) (map_mutatedCoordinate_neg k p a i))

private def mutationChartEquiv (a : ι → ℤ) : Chart ≃ₐ[k] Chart :=
  AlgEquiv.ofAlgHom (mutationOnChart k p a) (mutationOnChart k p (-a))
    (mutationOnChart_comp_neg k p a)
    (by simpa using mutationOnChart_comp_neg k p (-a))

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

/-- Pullback on the field of independent cluster X coordinates for mutation at `p`,
with `a i` the `(i,p)` entry of the exchange matrix. -/
def xMutation (a : ι → ℤ) : Functions ≃ₐ[k] Functions :=
  IsFractionRing.algEquivOfAlgEquiv (mutationChartEquiv k p a)

private def unitsToFunctions : Chartˣ →* Functionsˣ :=
  Units.map (algebraMap Chart Functions).toMonoidHom

private theorem coe_unitsToFunctions (u : Chartˣ) :
    (unitsToFunctions k p u : Functions) = algebraMap Chart Functions (u : Chart) :=
  Units.coe_map _ _

private theorem xMutation_coordinate (a : ι → ℤ) (i : ι) :
    xMutation k p a (xCoordinate k i) =
      (unitsToFunctions k p (mutatedCoordinate k p a i) : Functions) := by
  rw [xCoordinate_def, IsScalarTower.algebraMap_apply Laurent Chart Functions,
    xMutation, IsFractionRing.algEquivOfAlgEquiv_algebraMap, mutationChartEquiv,
    AlgEquiv.ofAlgHom_apply, ← coe_coordinateUnit, mutationOnChart_coordinate,
    coe_unitsToFunctions]

private theorem map_coordinateUnit_toFunctions (i : ι) :
    (unitsToFunctions k p (coordinateUnit k p i) : Functions) = xCoordinate k i := by
  rw [coe_unitsToFunctions, coe_coordinateUnit, ← IsScalarTower.algebraMap_apply, xCoordinate]

/-- The mutated coordinate pulls back to its reciprocal. -/
@[simp] theorem xMutation_apply_self (a : ι → ℤ) :
    xMutation k p a (xCoordinate k p) = (xCoordinate k p)⁻¹ := by
  rw [xMutation_coordinate, mutatedCoordinate_self, map_inv,
    Units.val_inv_eq_inv_val, map_coordinateUnit_toFunctions]

/-- The pullback of an X coordinate away from the mutation direction. -/
theorem xMutation_apply_of_ne (a : ι → ℤ) {i : ι} (hi : i ≠ p) :
    xMutation k p a (xCoordinate k i) =
      xCoordinate k i * (xCoordinate k p) ^ max (a i) 0 * (1 + xCoordinate k p) ^ (-a i) := by
  rw [xMutation_coordinate, mutatedCoordinate_of_ne _ _ _ hi]
  have hBin :
      (unitsToFunctions k p (binomialUnit k p) : Functions) = 1 + xCoordinate k p := by
    rw [coe_unitsToFunctions, coe_binomialUnit, map_add, map_one,
      ← coe_unitsToFunctions, map_coordinateUnit_toFunctions]
  simp only [map_mul, map_zpow, inverseBinomialUnit, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_coordinateUnit_toFunctions, hBin,
    mul_zpow, inv_zpow]
  rw [← zpow_neg, neg_neg]
  calc
    _ = xCoordinate k i * (xCoordinate k p) ^ max (a i) 0 *
        ((1 + xCoordinate k p) ^ max (-a i) 0 * (1 + xCoordinate k p) ^ (-max (a i) 0)) := by
      ac_rfl
    _ = _ := by
      have hExponent : max (-a i) 0 + -max (a i) 0 = -a i := by omega
      rw [← zpow_add₀ (one_add_xCoordinate_ne_zero k p), hExponent]

/-- Reversing the mutation negates the exchange column. -/
@[simp] theorem xMutation_symm (a : ι → ℤ) :
    (xMutation k p a).symm = xMutation k p (-a) := by
  simp only [xMutation, IsFractionRing.algEquivOfAlgEquiv_symm, mutationChartEquiv,
    AlgEquiv.ofAlgHom_symm, neg_neg]

/-- Pullback along the return mutation is the inverse of pullback along the original mutation. -/
theorem xMutation_symm_matrixMutation [DecidableEq ι] (B : Matrix ι ι ℤ) :
    (xMutation k p (fun i ↦ B i p)).symm =
      xMutation k p (fun i ↦ TauCeti.matrixMutation (Function.Embedding.refl ι) B p i p) := by
  simp [TauCeti.matrixMutation_apply_col, ← Pi.neg_def]

end QPainleve.Cluster
