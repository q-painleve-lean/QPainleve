/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Basic

import QPainleve.Algebra.MonoidAlgebra.BinomialTwist
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

private abbrev binomial : Laurent :=
  AddMonoidAlgebra.single (0 : B) 1 + AddMonoidAlgebra.single b 1

local notation "Chart" => Localization.Away (binomial k b)

private theorem binomial_ne_zero (hb : 1 + monomial k (ofAdd b) ≠ 0) : binomial k b ≠ 0 := by
  intro h
  apply hb
  have hone : algebraMap Laurent Functions (AddMonoidAlgebra.single 0 1) = 1 :=
    map_one (algebraMap Laurent Functions)
  simpa only [map_add, hone, map_zero, monomial_ofAdd] using
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
  IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.binomialTwist 1 1 b f hf)

/-- The shear pulls back a monomial by multiplying it by a power of the pivot binomial. -/
@[simp]
theorem binomialShear_monomial (f : B →+ ℤ) (hf : f b = 0) (x : B) :
    binomialShear k b hb f hf (monomial k (ofAdd x)) =
      monomial k (ofAdd x) * (1 + monomial k (ofAdd b)) ^ f x := by
  let : Fact (1 + monomial k (ofAdd b) ≠ 0) := ⟨hb⟩
  let M := algebraMap Chart Functions
  have hmon (x : B) : M (algebraMap Laurent Chart (AddMonoidAlgebra.single x 1)) =
      monomial k (ofAdd x) := by
    rw [← IsScalarTower.algebraMap_apply, monomial_ofAdd]
  have hbin : M (AddMonoidAlgebra.awayBinomialUnit (1 : k) 1 b : Chart) =
      1 + monomial k (ofAdd b) := by
    have hone : M (algebraMap Laurent Chart (AddMonoidAlgebra.single 0 1)) = 1 :=
      map_one (M.comp (algebraMap Laurent Chart))
    simp only [AddMonoidAlgebra.coe_awayBinomialUnit, map_add, hone, hmon]
  have hzpow : M ((AddMonoidAlgebra.awayBinomialUnit (1 : k) 1 b ^ f x : Chartˣ) : Chart) =
      (1 + monomial k (ofAdd b)) ^ f x := by
    calc
      _ = (Units.map M.toMonoidHom (AddMonoidAlgebra.awayBinomialUnit (1 : k) 1 b ^ f x) :
          Functions) := rfl
      _ = _ := by
        rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
        exact congrArg (· ^ f x) hbin
  rw [← hmon x, binomialShear, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    AddMonoidAlgebra.binomialTwist_single, map_mul, hzpow]

/-- The inverse shear negates the functional. -/
@[simp]
theorem binomialShear_symm (f : B →+ ℤ) (hf : f b = 0) :
    (binomialShear k b hb f hf).symm = binomialShear k b hb (-f) (by simp [hf]) := by
  let : Fact (1 + monomial k (ofAdd b) ≠ 0) := ⟨hb⟩
  unfold binomialShear
  rw [IsFractionRing.algEquivOfAlgEquiv_symm, AddMonoidAlgebra.binomialTwist_symm]

end QPainleve.CharacterTorus
