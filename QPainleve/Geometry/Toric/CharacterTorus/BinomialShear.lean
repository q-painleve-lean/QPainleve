/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Basic

import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.RingTheory.Localization.Away.FractionRing

/-!
# Binomial shears on character tori

If an integer functional vanishes on a pivot exponent, multiplying each monomial
by the corresponding power of the pivot binomial defines an automorphism of the open torus
where that binomial is invertible. When the binomial is nonzero, negating the functional
gives the inverse on the function field. The passage from the chart to the field uses
Tau Ceti's `Localization.Away.isFractionRing`, as in `QPainleve.Cluster.xMutation`.
-/

public noncomputable section

namespace QPainleve.CharacterTorus

open Multiplicative

variable (k : Type*) [Field k] {B : Type*} [AddCommGroup B] (b : B)

local notation "Laurent" => AddMonoidAlgebra k B
local notation "Functions" => FunctionField k B

private abbrev binomial : Laurent := 1 + AddMonoidAlgebra.single b 1

local notation "Chart" => Localization.Away (binomial k b)

private def chartMonomial : Multiplicative B →* Chartˣ :=
  ((algebraMap Laurent Chart).toMonoidHom.comp (AddMonoidAlgebra.of k B)).toHomUnits

private theorem coe_chartMonomial (x : B) :
    (chartMonomial k b (ofAdd x) : Chart) =
      algebraMap Laurent Chart (AddMonoidAlgebra.single x 1) := by
  simp [chartMonomial, AddMonoidAlgebra.of_apply]

private def chartBinomial : Chartˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Chart) (binomial k b)).unit

private theorem coe_chartBinomial :
    (chartBinomial k b : Chart) = 1 + (chartMonomial k b (ofAdd b) : Chart) := by
  simp [chartBinomial, coe_chartMonomial]

private def onLaurent (f : B →+ ℤ) : Laurent →ₐ[k] Chart :=
  AddMonoidAlgebra.lift k Chart B <| (Units.coeHom Chart).comp
    (chartMonomial k b * (zpowersHom Chartˣ (chartBinomial k b)).comp f.toMultiplicative)

private theorem onLaurent_single (f : B →+ ℤ) (x : B) :
    onLaurent k b f (AddMonoidAlgebra.single x 1) =
      ((chartMonomial k b (ofAdd x) * chartBinomial k b ^ f x : Chartˣ) : Chart) := by
  simp [onLaurent, zpowersHom_apply]

private def onChart (f : B →+ ℤ) (hf : f b = 0) : Chart →ₐ[k] Chart :=
  IsLocalization.Away.liftAlgHom (binomial k b) (f := onLaurent k b f) (by
    rw [map_add, map_one, onLaurent_single, hf, zpow_zero, mul_one, ← coe_chartBinomial]
    exact (chartBinomial k b).isUnit)

private theorem onChart_monomial (f : B →+ ℤ) (hf : f b = 0) (x : B) :
    onChart k b f hf (chartMonomial k b (ofAdd x) : Chart) =
      ((chartMonomial k b (ofAdd x) * chartBinomial k b ^ f x : Chartˣ) : Chart) := by
  simp [coe_chartMonomial, onChart, onLaurent_single]

private theorem map_chartMonomial (f : B →+ ℤ) (hf : f b = 0) (x : B) :
    Units.map (onChart k b f hf).toMonoidHom (chartMonomial k b (ofAdd x)) =
      chartMonomial k b (ofAdd x) * chartBinomial k b ^ f x :=
  Units.ext (onChart_monomial k b f hf x)

private theorem map_chartBinomial (f : B →+ ℤ) (hf : f b = 0) :
    Units.map (onChart k b f hf).toMonoidHom (chartBinomial k b) = chartBinomial k b := by
  apply Units.ext
  simp [coe_chartBinomial, onChart_monomial, hf]

private theorem onChart_comp_neg (f : B →+ ℤ) (hf : f b = 0) :
    (onChart k b f hf).comp (onChart k b (-f) (by simp [hf])) = AlgHom.id k Chart := by
  apply Localization.algHom_ext
  apply (AddMonoidAlgebra.lift k Chart B).symm.injective
  apply MonoidHom.ext
  intro x
  have h (a : B) :
      Units.map (onChart k b f hf).toMonoidHom
        (chartMonomial k b (ofAdd a) * chartBinomial k b ^ (-f) a) =
        chartMonomial k b (ofAdd a) := by
    rw [map_mul, map_zpow, map_chartMonomial, map_chartBinomial, mul_assoc, ← zpow_add]
    simp
  have hc := congrArg (fun u : Chartˣ ↦ (u : Chart)) (h x.toAdd)
  simp only [Units.coe_map] at hc
  simp only [AddMonoidAlgebra.lift_symm_apply, AlgHom.comp_apply, AlgHom.id_apply]
  -- The structural algebra hom in localization extensionality is the chart's algebra map.
  change onChart k b f hf (onChart k b (-f) _
    (algebraMap Laurent Chart (AddMonoidAlgebra.single x.toAdd 1))) =
      algebraMap Laurent Chart (AddMonoidAlgebra.single x.toAdd 1)
  rw [← coe_chartMonomial, onChart_monomial]
  exact hc

private def chartEquiv (f : B →+ ℤ) (hf : f b = 0) : Chart ≃ₐ[k] Chart :=
  AlgEquiv.ofAlgHom (onChart k b f hf) (onChart k b (-f) (by simp [hf]))
    (onChart_comp_neg k b f hf) (by
      simpa only [neg_neg] using onChart_comp_neg k b (-f) (by simp [hf]))

private theorem binomial_ne_zero (hb : 1 + monomial k (ofAdd b) ≠ 0) : binomial k b ≠ 0 := by
  intro h
  apply hb
  simpa only [map_add, map_one, map_zero, monomial_ofAdd] using
    congrArg (algebraMap Laurent Functions) h

variable [Module.Free ℤ B]

local instance shearHasUniqueDiv {G : Type*} [AddCommGroup G] [Module ℤ G]
    [Module.Free ℤ G] : HasUniqueDiv G :=
  .of_isTorsionFree ℤ G

section

variable [Fact (1 + monomial k (ofAdd b) ≠ 0)]

private instance chartAlgebra : Algebra Chart Functions :=
  Localization.Away.algebraOfIsFractionRing Functions (binomial_ne_zero k b Fact.out)

private instance chartLaurentTower : IsScalarTower Laurent Chart Functions :=
  Localization.Away.isScalarTower_of_isFractionRing Functions (binomial_ne_zero k b Fact.out)

private instance chartTower : IsScalarTower k Chart Functions :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k Laurent Chart, ← RingHom.comp_apply,
      ← IsScalarTower.algebraMap_eq Laurent Chart Functions, ← IsScalarTower.algebraMap_apply]

private instance chartFractionRing : IsFractionRing Chart Functions :=
  Localization.Away.isFractionRing Functions (binomial_ne_zero k b Fact.out)

end

variable (hb : 1 + monomial k (ofAdd b) ≠ 0)

/-- Pullback multiplying each character by a power of the pivot binomial. -/
def binomialShear (f : B →+ ℤ) (hf : f b = 0) : Functions ≃ₐ[k] Functions :=
  let : Fact (1 + monomial k (ofAdd b) ≠ 0) := ⟨hb⟩
  IsFractionRing.algEquivOfAlgEquiv (chartEquiv k b f hf)

/-- The shear pulls back a monomial by multiplying it by a power of the pivot binomial. -/
@[simp]
theorem binomialShear_monomial (f : B →+ ℤ) (hf : f b = 0) (x : B) :
    binomialShear k b hb f hf (monomial k (ofAdd x)) =
      monomial k (ofAdd x) * (1 + monomial k (ofAdd b)) ^ f x := by
  let : Fact (1 + monomial k (ofAdd b) ≠ 0) := ⟨hb⟩
  let M := algebraMap Chart Functions
  have hmon (x : B) : M (chartMonomial k b (ofAdd x) : Chart) = monomial k (ofAdd x) := by
    rw [coe_chartMonomial, ← IsScalarTower.algebraMap_apply, monomial_ofAdd]
  have hbin : M (chartBinomial k b : Chart) = 1 + monomial k (ofAdd b) := by
    rw [coe_chartBinomial, map_add, map_one, hmon]
  have hzpow : M ((chartBinomial k b ^ f x : Chartˣ) : Chart) =
      (1 + monomial k (ofAdd b)) ^ f x := by
    calc
      _ = (Units.map M.toMonoidHom (chartBinomial k b ^ f x) : Functions) := rfl
      _ = _ := by
        rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
        exact congrArg (· ^ f x) hbin
  rw [← hmon x, binomialShear, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    chartEquiv, AlgEquiv.ofAlgHom_apply, onChart_monomial, Units.val_mul, map_mul, hzpow]

/-- The inverse shear negates the functional. -/
@[simp]
theorem binomialShear_symm (f : B →+ ℤ) (hf : f b = 0) :
    (binomialShear k b hb f hf).symm = binomialShear k b hb (-f) (by simp [hf]) := by
  let : Fact (1 + monomial k (ofAdd b) ≠ 0) := ⟨hb⟩
  unfold binomialShear
  rw [IsFractionRing.algEquivOfAlgEquiv_symm]
  congr 1
  exact AlgEquiv.ext fun _ ↦ rfl

end QPainleve.CharacterTorus
