/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Picard.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import Mathlib.Algebra.Group.Subgroup.Finsupp

/-!
# The Picard presentation of a regular toric fan

The boundary divisors of the complex scheme of a nonempty regular fan generate its Picard
group. Every relation is the divisor of a character, with coefficients given by evaluating
the character on the primitive ray generators.

The proof uses Tau Ceti's open-immersion Picard excision, its Weil-to-Picard comparison
and the classification of units of a group algebra. The divisor sequence is the one in
Cox, Little and Schenck, *Toric Varieties*, Theorem 4.1.3, specialized to regular fans.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint LineBundleClass SchemeWeilDivisor WeilDivisor)
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor (orderAt_apply)

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The coefficients of the divisor of a character at the rays of the fan. -/
def characterToRayDivisor : (N →+ ℤ) →+ (Φ.Ray → ℤ) :=
  AddMonoidHom.pi fun ρ ↦ AddMonoidHom.eval ρ.primitiveGenerator

@[simp]
theorem characterToRayDivisor_apply (m : N →+ ℤ) (ρ : Φ.Ray) :
    Φ.characterToRayDivisor m ρ = m ρ.primitiveGenerator := (rfl)

/-- Regard an integer family on the rays as a Weil divisor on the toric scheme. -/
def rayDivisorToWeilDivisor (hΦ : Φ.IsRegular) :
    (Φ.Ray → ℤ) →+ SchemeWeilDivisor Φ.algebraicRealization :=
  (WeilDivisor.pushforward (Φ.rayBoundaryPoint hΦ)).comp
    (Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm.toLinearMap.toAddMonoidHom

@[simp]
theorem coeff_rayDivisorToWeilDivisor (hΦ : Φ.IsRegular) (a : Φ.Ray → ℤ) (ρ : Φ.Ray) :
    WeilDivisor.coeff (Φ.rayDivisorToWeilDivisor hΦ a) (Φ.rayBoundaryPoint hΦ ρ) = a ρ := by
  simpa [rayDivisorToWeilDivisor, WeilDivisor.pushforward_apply, WeilDivisor.coeff] using
    Finsupp.mapDomain_apply_of_injective (Φ.rayBoundaryPoint_injective hΦ)
      ((Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm a) ρ

/-- A ray divisor has zero coefficient at any codimension-one point outside the ray boundary. -/
theorem coeff_rayDivisorToWeilDivisor_of_notMem_range (hΦ : Φ.IsRegular)
    (a : Φ.Ray → ℤ) {x : CodimensionOnePoint Φ.algebraicRealization}
    (hx : x ∉ Set.range (Φ.rayBoundaryPoint hΦ)) :
    WeilDivisor.coeff (Φ.rayDivisorToWeilDivisor hΦ a) x = 0 := by
  simpa [rayDivisorToWeilDivisor, WeilDivisor.pushforward_apply, WeilDivisor.coeff] using
    Finsupp.mapDomain_of_notMem_range ((Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm a) x hx

variable [Nonempty Φ.cones]

/-- The class in the native Picard group of a divisor supported on the toric boundary. -/
def rayDivisorToPicard (hΦ : Φ.IsRegular) :
    (Φ.Ray → ℤ) →+ Additive (LineBundleClass Φ.algebraicRealization) :=
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  (weilToLineBundleClassHom Φ.algebraicRealization).comp (Φ.rayDivisorToWeilDivisor hΦ)

/-- A divisor concentrated on one ray maps to the corresponding multiple of its prime class. -/
@[simp]
theorem rayDivisorToPicard_single (hΦ : Φ.IsRegular) [DecidableEq Φ.Ray] (ρ : Φ.Ray) (n : ℤ) :
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    Φ.rayDivisorToPicard hΦ (Pi.single ρ n) =
      n • Additive.ofMul (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) := by
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  simp [rayDivisorToPicard, rayDivisorToWeilDivisor, WeilDivisor.pushforward_apply,
    LineBundleClass.primeDivisorClass_def]

/-- The class of a ray divisor is the sum of the corresponding prime-divisor classes. -/
theorem rayDivisorToPicard_apply (hΦ : Φ.IsRegular) [Fintype Φ.Ray] (a : Φ.Ray → ℤ) :
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    Φ.rayDivisorToPicard hΦ a =
      ∑ ρ, a ρ • Additive.ofMul (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) := by
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  classical
  calc
    Φ.rayDivisorToPicard hΦ a = Φ.rayDivisorToPicard hΦ (∑ ρ, Pi.single ρ (a ρ)) := by
      rw [Finset.univ_sum_single]
    _ = _ := by simp

/-- The boundary divisor classes generate the Picard group of a nonempty regular fan. -/
theorem rayDivisorToPicard_surjective (hΦ : Φ.IsRegular) :
    Function.Surjective (Φ.rayDivisorToPicard hΦ) := by
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := Fintype.ofFinite Φ.Ray
  intro L
  let j := Φ.denseTorusι inferInstance
  have htrivial : LineBundleClass.pullback j L.toMul = 1 := Subsingleton.elim _ _
  have hpoints (x : CodimensionOnePoint Φ.algebraicRealization) :
      x.val ∉ Set.range j ↔ x ∈ Set.range (Φ.rayBoundaryPoint hΦ) := by
    rw [Φ.range_rayBoundaryPoint hΦ inferInstance]
    rfl
  have hset : {LineBundleClass.primeDivisorClass x |
      (x : CodimensionOnePoint Φ.algebraicRealization)
      (_ : x.val ∉ Set.range j)} =
      Set.range (fun ρ : Φ.Ray ↦ LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨ρ, rfl⟩ := (hpoints x).1 hx
      exact ⟨ρ, rfl⟩
    · rintro ⟨ρ, rfl⟩
      exact ⟨Φ.rayBoundaryPoint hΦ ρ, (hpoints _).2 (Set.mem_range_self ρ), rfl⟩
  have hmem := (LineBundleClass.pullback_eq_one_iff_mem_closure_of_isOpenImmersion j).1 htrivial
  rw [hset, Subgroup.mem_closure_range_iff_of_fintype] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, Additive.toMul.injective ?_⟩
  rw [Φ.rayDivisorToPicard_apply hΦ a, toMul_sum]
  simpa using ha.symm

section Principal

local notation "𝒳" => Φ.algebraicRealization
local notation "𝕋" => Φ.denseTorus

local instance : IsLocallyNoetherian 𝕋 :=
  isLocallyNoetherian_of_isOpenImmersion (Φ.denseTorusι inferInstance)

/-- The principal Weil divisor of a toric character has the prescribed ray coefficients. -/
theorem rayDivisorToWeilDivisor_characterToRayDivisor (hΦ : Φ.IsRegular) (m : N →+ ℤ) :
    Φ.rayDivisorToWeilDivisor hΦ (Φ.characterToRayDivisor m) =
      (WeilDivisor.OrderSystem.ofScheme 𝒳).principalDivisor
        (Additive.ofMul (Φ.character.toHomUnits (ofAdd m))) := by
  apply WeilDivisor.ext
  intro x
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
    orderAt_apply, toMul_ofMul, MonoidHom.coe_toHomUnits]
  by_cases hx : x ∈ Set.range (Φ.rayBoundaryPoint hΦ)
  · obtain ⟨ρ, rfl⟩ := hx
    rw [Φ.coeff_rayDivisorToWeilDivisor, Φ.characterToRayDivisor_apply,
      Φ.ord_rayBoundaryPoint_character hΦ]
  · rw [Φ.coeff_rayDivisorToWeilDivisor_of_notMem_range hΦ _ hx]
    apply (Φ.ord_character_eq_zero_of_mem_range_denseTorusι m ?_).symm
    simpa [Φ.range_rayBoundaryPoint hΦ inferInstance] using hx

/-- The character divisor map and the boundary class map are exact. -/
theorem exact_characterToRayDivisor_rayDivisorToPicard (hΦ : Φ.IsRegular) :
    Function.Exact Φ.characterToRayDivisor (Φ.rayDivisorToPicard hΦ) := by
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let j := Φ.denseTorusι inferInstance
  intro a
  rw [rayDivisorToPicard, AddMonoidHom.comp_apply, ← AddMonoidHom.mem_ker,
    ker_weilToLineBundleClassHom, WeilDivisor.OrderSystem.mem_principalSubgroup]
  constructor
  · rintro ⟨f, hf⟩
    have hzero (y : CodimensionOnePoint 𝕋) :
        (𝕋).ord (j.functionFieldMap (f.toMul : (𝒳).functionField)) y.val = 0 := by
      rw [ord_functionFieldMap j, ← CodimensionOnePoint.coe_mapOfIsOpenImmersion j,
        ← orderAt_apply, ← WeilDivisor.OrderSystem.ofScheme_ord,
        ← WeilDivisor.OrderSystem.coeff_principalDivisor, hf]
      apply Φ.coeff_rayDivisorToWeilDivisor_of_notMem_range hΦ
      rw [Φ.range_rayBoundaryPoint hΦ inferInstance]
      exact fun hy ↦ hy ⟨y, CodimensionOnePoint.coe_mapOfIsOpenImmersion j y |>.symm⟩
    obtain ⟨s, m, hfm⟩ := Φ.exists_eq_const_mul_character f.toMul hzero
    refine ⟨m, funext fun ρ ↦ ?_⟩
    have hρ := congrArg (fun D ↦ WeilDivisor.coeff D (Φ.rayBoundaryPoint hΦ ρ)) hf
    rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
      orderAt_apply, Φ.coeff_rayDivisorToWeilDivisor,
      hfm, Scheme.ord_mul (s.isUnit.map ((𝒳).germToFunctionField ⊤).hom).ne_zero
        ((Group.isUnit (ofAdd m)).map Φ.character).ne_zero,
      (𝒳).ord_of_isUnit s.isUnit trivial, zero_add, Φ.ord_rayBoundaryPoint_character hΦ] at hρ
    exact hρ
  · rintro ⟨m, rfl⟩
    exact ⟨Additive.ofMul (Φ.character.toHomUnits (ofAdd m)),
      (Φ.rayDivisorToWeilDivisor_characterToRayDivisor hΦ m).symm⟩

end Principal

end TauCeti.Toric.Fan
