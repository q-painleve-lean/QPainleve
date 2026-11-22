/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

/-!
# Open charts for cluster X mutation

Mutation in direction `p` is defined on the Laurent chart where `1 + Xₚ` is invertible.
The chart automorphism commutes with change of coefficients, including reduction from
the integral chart to a field of positive characteristic.

The coordinate formula is that of Fock and Goncharov, *Cluster ensembles,
quantization and the dilogarithm*, §1.2.2 (7) and §1.2.4 (13).
The chart construction uses Tau Ceti's `LaurentRing.aeval` and the universal property
of the localization.
-/

public noncomputable section

namespace QPainleve.Cluster

open TauCeti LaurentRing

variable (R : Type*) [CommSemiring R] {ι : Type*} (p : ι)

/-- The Laurent coordinate ring with the mutation binomial `1 + Xₚ` inverted. -/
abbrev XMutationChart :=
  Localization.Away (1 + (X p : LaurentRing R ι))

local notation "Chart" => XMutationChart

/-- A Laurent coordinate as a unit of the mutation chart. -/
def xMutationChartUnitX (i : ι) : (Chart R p)ˣ :=
  Units.map (algebraMap (LaurentRing R ι) (Chart R p)).toMonoidHom (unitX i)

@[simp]
theorem val_xMutationChartUnitX (i : ι) :
    (xMutationChartUnitX R p i : Chart R p) =
      algebraMap (LaurentRing R ι) (Chart R p) (X i) := by
  simp [xMutationChartUnitX]

/-- The inverted binomial as a unit of the mutation chart. -/
def xMutationChartBinomial : (Chart R p)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Chart R p)
    (1 + (X p : LaurentRing R ι))).unit

@[simp]
theorem val_xMutationChartBinomial :
    (xMutationChartBinomial R p : Chart R p) =
      1 + (xMutationChartUnitX R p p : Chart R p) := by
  simp [xMutationChartBinomial]

private def mutatedUnit (a : ι → ℤ) (i : ι) : (Chart R p)ˣ := by
  classical
  exact if i = p then (xMutationChartUnitX R p p)⁻¹
    else xMutationChartUnitX R p i * xMutationChartUnitX R p p ^ max (a i) 0 *
      xMutationChartBinomial R p ^ (-a i)

private theorem coe_inv_mul_binomial :
    (↑((xMutationChartUnitX R p p)⁻¹ * xMutationChartBinomial R p) : Chart R p) =
      1 + (↑((xMutationChartUnitX R p p)⁻¹) : Chart R p) := by
  simp only [Units.val_mul, val_xMutationChartBinomial, mul_add, mul_one, Units.inv_mul]
  exact add_comm _ _

private def mutationOnChart (a : ι → ℤ) : Chart R p →ₐ[R] Chart R p :=
  IsLocalization.Away.liftAlgHom (1 + (X p : LaurentRing R ι))
    (f := aeval (mutatedUnit R p a)) (by
      simp only [map_add, map_one, aeval_X, mutatedUnit, ite_true]
      exact ⟨_, coe_inv_mul_binomial R p⟩)

private theorem map_mutationOnChart_unitX (a : ι → ℤ) (i : ι) :
    Units.map (mutationOnChart R p a : Chart R p →* Chart R p) (xMutationChartUnitX R p i) =
      mutatedUnit R p a i := by
  apply Units.ext
  simp [mutationOnChart]

private theorem map_mutationOnChart_binomial (a : ι → ℤ) :
    Units.map (mutationOnChart R p a : Chart R p →* Chart R p) (xMutationChartBinomial R p) =
      (xMutationChartUnitX R p p)⁻¹ * xMutationChartBinomial R p := by
  apply Units.ext
  have hp := congrArg Units.val (map_mutationOnChart_unitX R p a p)
  simp only [Units.coe_map, MonoidHom.coe_ofClass, mutatedUnit, ite_true] at hp
  simpa only [Units.coe_map, MonoidHom.coe_ofClass, val_xMutationChartBinomial, map_add,
    map_one, coe_inv_mul_binomial] using congrArg (1 + ·) hp

private theorem map_mutatedUnit_neg (a : ι → ℤ) (i : ι) :
    Units.map (mutationOnChart R p a : Chart R p →* Chart R p) (mutatedUnit R p (-a) i) =
      xMutationChartUnitX R p i := by
  by_cases hi : i = p
  · subst i
    simp only [mutatedUnit, ite_true, map_inv, map_mutationOnChart_unitX, inv_inv]
  · simp only [mutatedUnit, hi, ite_false, Pi.neg_apply, neg_neg, map_mul, map_zpow,
      map_mutationOnChart_unitX, map_mutationOnChart_binomial, ite_true, mul_zpow, inv_zpow,
      ← zpow_neg]
    calc
      _ = xMutationChartUnitX R p i *
          ((xMutationChartUnitX R p p ^ max (a i) 0 *
            xMutationChartUnitX R p p ^ (-max (-a i) 0)) *
            xMutationChartUnitX R p p ^ (-a i)) *
          (xMutationChartBinomial R p ^ (-a i) * xMutationChartBinomial R p ^ a i) := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by
        simp only [← zpow_add]
        have h : max (a i) 0 + -max (-a i) 0 + -a i = 0 := by omega
        simp [h]

private theorem mutationOnChart_comp_neg (a : ι → ℤ) :
    (mutationOnChart R p a).comp (mutationOnChart R p (-a)) = AlgHom.id R _ := by
  apply Localization.algHom_ext
  apply LaurentRing.algHom_ext
  intro i
  have h :
      Units.map (mutationOnChart R p a : Chart R p →* Chart R p)
        (Units.map (mutationOnChart R p (-a) : Chart R p →* Chart R p)
          (xMutationChartUnitX R p i)) = xMutationChartUnitX R p i := by
    rw [map_mutationOnChart_unitX, map_mutatedUnit_neg]
  simpa only [Units.coe_map, MonoidHom.coe_ofClass, AlgHom.comp_apply, AlgHom.id_apply,
    val_xMutationChartUnitX, Algebra.algHom, IsScalarTower.toAlgHom_apply] using
    congrArg Units.val h

/-- X mutation on the open Laurent chart. The entry `a i` is the exchange entry at `(i,p)`. -/
def xMutationChartEquiv (a : ι → ℤ) : Chart R p ≃ₐ[R] Chart R p :=
  AlgEquiv.ofAlgHom (mutationOnChart R p a) (mutationOnChart R p (-a))
    (mutationOnChart_comp_neg R p a)
    (by simpa using mutationOnChart_comp_neg R p (-a))

/-- Negating the exchange column gives the inverse chart automorphism. -/
@[simp]
theorem xMutationChartEquiv_symm (a : ι → ℤ) :
    (xMutationChartEquiv R p a).symm = xMutationChartEquiv R p (-a) := by
  simp [xMutationChartEquiv, AlgEquiv.ofAlgHom_symm]

/-- Mutation inverts the unit at the pivot. -/
@[simp]
theorem map_xMutationChartUnitX_self (a : ι → ℤ) :
    Units.map (xMutationChartEquiv R p a : Chart R p →* Chart R p)
      (xMutationChartUnitX R p p) = (xMutationChartUnitX R p p)⁻¹ := by
  apply Units.ext
  simpa only [Units.coe_map, MonoidHom.coe_ofClass, xMutationChartEquiv,
    AlgEquiv.ofAlgHom_apply, mutatedUnit, ite_true] using
    congrArg Units.val (map_mutationOnChart_unitX R p a p)

/-- The X-mutation formula for a unit away from the pivot. -/
theorem map_xMutationChartUnitX_of_ne (a : ι → ℤ) {i : ι} (hi : i ≠ p) :
    Units.map (xMutationChartEquiv R p a : Chart R p →* Chart R p)
      (xMutationChartUnitX R p i) =
      xMutationChartUnitX R p i * xMutationChartUnitX R p p ^ max (a i) 0 *
        xMutationChartBinomial R p ^ (-a i) := by
  apply Units.ext
  simpa only [Units.coe_map, MonoidHom.coe_ofClass, xMutationChartEquiv,
    AlgEquiv.ofAlgHom_apply, mutatedUnit, hi, ite_false] using
    congrArg Units.val (map_mutationOnChart_unitX R p a i)

/-- The localized binomial pulls back to `Xₚ⁻¹(1 + Xₚ)`. -/
@[simp]
theorem map_xMutationChartBinomial (a : ι → ℤ) :
    Units.map (xMutationChartEquiv R p a : Chart R p →* Chart R p)
      (xMutationChartBinomial R p) =
      (xMutationChartUnitX R p p)⁻¹ * xMutationChartBinomial R p := by
  apply Units.ext
  simpa only [Units.coe_map, MonoidHom.coe_ofClass, xMutationChartEquiv,
    AlgEquiv.ofAlgHom_apply] using congrArg Units.val (map_mutationOnChart_binomial R p a)

variable {R} {S : Type*} [CommSemiring S]

/-- Change the coefficients of a mutation chart along a semiring homomorphism. -/
def xMutationChartMap (f : R →+* S) : Chart R p →+* Chart S p :=
  IsLocalization.Away.lift (1 + (X p : LaurentRing R ι))
    (g := (algebraMap (LaurentRing S ι) (Chart S p)).comp
      (AddMonoidAlgebra.mapRingHom (ι →₀ ℤ) f))
    (by simpa using (xMutationChartBinomial S p).isUnit)

/-- Change of coefficients extends the coefficient map on Laurent polynomials. -/
@[simp]
theorem xMutationChartMap_algebraMap (f : R →+* S) (x : LaurentRing R ι) :
    xMutationChartMap p f (algebraMap (LaurentRing R ι) (Chart R p) x) =
      algebraMap (LaurentRing S ι) (Chart S p)
        (AddMonoidAlgebra.mapRingHom (ι →₀ ℤ) f x) := by
  simp [xMutationChartMap]

@[simp]
theorem map_xMutationChartUnitX (f : R →+* S) (i : ι) :
    Units.map (xMutationChartMap p f : Chart R p →* Chart S p) (xMutationChartUnitX R p i) =
      xMutationChartUnitX S p i := by
  apply Units.ext
  simp

@[simp]
theorem map_xMutationChartBinomial_coeff (f : R →+* S) :
    Units.map (xMutationChartMap p f : Chart R p →* Chart S p) (xMutationChartBinomial R p) =
      xMutationChartBinomial S p := by
  apply Units.ext
  simp

/-- Mutation commutes with coefficient change on the open chart. In particular the
integral chart automorphism specializes along `ℤ → k` for every field `k`. -/
theorem xMutationChartMap_xMutationChartEquiv (f : R →+* S) (a : ι → ℤ)
    (x : Chart R p) :
    xMutationChartMap p f (xMutationChartEquiv R p a x) =
      xMutationChartEquiv S p a (xMutationChartMap p f x) := by
  let : Algebra R (Chart S p) := ((algebraMap S (Chart S p)).comp f).toAlgebra
  let baseChange : Chart R p →ₐ[R] Chart S p :=
    { toRingHom := xMutationChartMap p f
      commutes' r := by
        simp [RingHom.algebraMap_toAlgebra,
          IsScalarTower.algebraMap_apply R (LaurentRing R ι) (Chart R p),
          IsScalarTower.algebraMap_apply S (LaurentRing S ι) (Chart S p)] }
  let targetMutation : Chart S p →ₐ[R] Chart S p :=
    { toRingHom := xMutationChartEquiv S p a
      commutes' r := by simp [RingHom.algebraMap_toAlgebra] }
  suffices baseChange.comp (xMutationChartEquiv R p a).toAlgHom =
      targetMutation.comp baseChange from AlgHom.congr_fun this x
  apply Localization.algHom_ext
  apply LaurentRing.algHom_ext
  intro i
  let fUnits := Units.map (xMutationChartMap p f : Chart R p →* Chart S p)
  have h :
      fUnits (Units.map (xMutationChartEquiv R p a : Chart R p →* Chart R p)
        (xMutationChartUnitX R p i)) =
      Units.map (xMutationChartEquiv S p a : Chart S p →* Chart S p)
        (fUnits (xMutationChartUnitX R p i)) := by
    by_cases hi : i = p
    · subst i
      simp [fUnits]
    · simp [fUnits, map_xMutationChartUnitX_of_ne _ _ _ hi]
  simpa only [baseChange, targetMutation, fUnits, AlgHom.coe_mk, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, RingHom.coe_coe, Units.coe_map, MonoidHom.coe_ofClass,
    val_xMutationChartUnitX, Algebra.algHom, IsScalarTower.toAlgHom_apply] using
    congrArg Units.val h

end QPainleve.Cluster
