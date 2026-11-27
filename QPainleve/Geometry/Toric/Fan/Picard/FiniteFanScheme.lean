/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.Excision
public import QPainleve.Geometry.Toric.BaseChange.Fan
public import QPainleve.Geometry.Toric.Fan.Boundary.Character
public import QPainleve.Geometry.Toric.Fan.Picard.Basic

/-!
# The Picard group of a regular fan over a factorial coefficient ring

Over a Noetherian factorial domain, every line bundle class is a sum of classes of
ray divisors. The relations are the principal divisors of lattice characters.
This identifies the Picard group with the quotient of the free abelian group on the
rays by the pairing with the primitive generators.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry (CodimensionOnePoint LineBundleClass SchemeWeilDivisor WeilDivisor)
open TauCeti.AlgebraicGeometry.Scheme (ord_functionFieldMap)
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor (orderAt_apply)

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i)

/-- Regard an integer family on the rays as a Weil divisor on the toric scheme. -/
def rayChartDivisorToWeilDivisor (hΦ : Φ.IsRegular) :
    (Φ.Ray → ℤ) →+ SchemeWeilDivisor (Φ.finiteFanScheme R) :=
  (WeilDivisor.pushforward (Φ.rayBoundaryChartPoint (R := R) hΦ)).comp
    (Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm.toLinearMap.toAddMonoidHom

@[simp]
theorem coeff_rayChartDivisorToWeilDivisor (hΦ : Φ.IsRegular) (a : Φ.Ray → ℤ) (ρ : Φ.Ray) :
    WeilDivisor.coeff (Φ.rayChartDivisorToWeilDivisor R hΦ a)
      (Φ.rayBoundaryChartPoint (R := R) hΦ ρ) = a ρ := by
  simpa [rayChartDivisorToWeilDivisor, WeilDivisor.pushforward_apply, WeilDivisor.coeff] using
    Finsupp.mapDomain_apply_of_injective (Φ.rayBoundaryChartPoint_injective (R := R) hΦ)
      ((Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm a) ρ

/-- A ray divisor has zero coefficient at any codimension-one point outside the ray boundary. -/
theorem coeff_rayChartDivisorToWeilDivisor_of_notMem_range (hΦ : Φ.IsRegular)
    (a : Φ.Ray → ℤ) {x : CodimensionOnePoint (Φ.finiteFanScheme R)}
    (hx : x ∉ Set.range (Φ.rayBoundaryChartPoint (R := R) hΦ)) :
    WeilDivisor.coeff (Φ.rayChartDivisorToWeilDivisor R hΦ a) x = 0 := by
  simpa [rayChartDivisorToWeilDivisor, WeilDivisor.pushforward_apply, WeilDivisor.coeff] using
    Finsupp.mapDomain_of_notMem_range ((Finsupp.linearEquivFunOnFinite ℤ ℤ Φ.Ray).symm a) x hx

variable [h₀ : Nonempty Φ.cones] [UniqueFactorizationMonoid R]

/-- The Picard class of a divisor supported on the toric boundary. -/
def rayChartDivisorToPicard (hΦ : Φ.IsRegular) :
    (Φ.Ray → ℤ) →+ Additive (LineBundleClass (Φ.finiteFanScheme R)) :=
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  (weilToLineBundleClassHom (Φ.finiteFanScheme R)).comp (Φ.rayChartDivisorToWeilDivisor R hΦ)

/-- The Picard class of a ray divisor is the line-bundle class of the associated Weil divisor. -/
theorem rayChartDivisorToPicard_def (hΦ : Φ.IsRegular) (a : Φ.Ray → ℤ) :
    letI := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
    Φ.rayChartDivisorToPicard R hΦ a =
      weilToLineBundleClassHom (Φ.finiteFanScheme R) (Φ.rayChartDivisorToWeilDivisor R hΦ a) :=
  (rfl)

/-- A divisor supported on a single ray maps to a multiple of its prime class. -/
theorem rayChartDivisorToPicard_single (hΦ : Φ.IsRegular) [DecidableEq Φ.Ray]
    (ρ : Φ.Ray) (n : ℤ) :
    letI := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
    Φ.rayChartDivisorToPicard R hΦ (Pi.single ρ n) =
      n • Additive.ofMul (LineBundleClass.primeDivisorClass
        (Φ.rayBoundaryChartPoint (R := R) hΦ ρ)) := by
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  simp [rayChartDivisorToPicard, rayChartDivisorToWeilDivisor, WeilDivisor.pushforward_apply,
    LineBundleClass.primeDivisorClass_def]

/-- The class of a ray divisor is the sum of the corresponding prime-divisor classes. -/
theorem rayChartDivisorToPicard_apply (hΦ : Φ.IsRegular) [Fintype Φ.Ray] (a : Φ.Ray → ℤ) :
    letI := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
    Φ.rayChartDivisorToPicard R hΦ a =
      ∑ ρ, a ρ • Additive.ofMul (LineBundleClass.primeDivisorClass
        (Φ.rayBoundaryChartPoint (R := R) hΦ ρ)) := by
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  exact LineBundleClass.weilToLineBundleClassHom_pushforward_apply
    (Φ.rayBoundaryChartPoint (R := R) hΦ) a

/-- The boundary divisor classes generate the Picard group of a nonempty regular fan. -/
theorem rayChartDivisorToPicard_surjective (hΦ : Φ.IsRegular) :
    Function.Surjective (Φ.rayChartDivisorToPicard R hΦ) := by
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  let hbot := Φ.bot_mem h₀.some.property
  have := (isRegularCone_bot Φ.lattice).subsingleton_lineBundleClass_affineChart Φ.lattice R
  exact LineBundleClass.surjective_weilToLineBundleClassHom_of_complement
    (Φ.affineChartι R ⟨⊥, hbot⟩) (Φ.rayBoundaryChartPoint (R := R) hΦ)
    (Φ.range_rayBoundaryChartPoint (R := R) hΦ hbot)

section Principal

local notation "𝒳" => (Φ.finiteFanScheme R)
local notation "botCone" =>
  (Subtype.mk (⊥ : PointedCone ℝ V) (Φ.bot_mem h₀.some.property) : Φ.cones)
local notation "𝕋" => (affineChart R Φ.lattice (⊥ : PointedCone ℝ V))
local notation "zeroChart" => (Φ.affineChartι R botCone)

local instance : IsLocallyNoetherian 𝕋 := isLocallyNoetherian_of_isOpenImmersion zeroChart

omit [UniqueFactorizationMonoid R] in
/-- The principal Weil divisor of a toric character has the prescribed ray coefficients. -/
theorem rayChartDivisorToWeilDivisor_characterToRayDivisor (hΦ : Φ.IsRegular) (m : N →+ ℤ) :
    Φ.rayChartDivisorToWeilDivisor R hΦ (Φ.characterToRayDivisor m) =
      (WeilDivisor.OrderSystem.ofScheme 𝒳).principalDivisor
        (Additive.ofMul ((Φ.functionFieldCharacter R).toHomUnits (ofAdd m))) := by
  apply WeilDivisor.ext
  intro x
  rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
    orderAt_apply, toMul_ofMul, MonoidHom.coe_toHomUnits]
  by_cases hx : x ∈ Set.range (Φ.rayBoundaryChartPoint (R := R) hΦ)
  · obtain ⟨ρ, rfl⟩ := hx
    rw [Φ.coeff_rayChartDivisorToWeilDivisor R hΦ, Φ.characterToRayDivisor_apply,
      Φ.ord_rayBoundaryChartPoint_character R hΦ]
  · rw [Φ.coeff_rayChartDivisorToWeilDivisor_of_notMem_range R hΦ _ hx]
    apply (Φ.ord_functionFieldCharacter_eq_zero_of_mem_range_zeroChart R m ?_).symm
    simpa [Φ.range_rayBoundaryChartPoint (R := R) hΦ (Φ.bot_mem h₀.some.property)] using hx

/-- The character divisor map and the boundary class map are exact. -/
theorem exact_characterToRayDivisor_rayChartDivisorToPicard (hΦ : Φ.IsRegular) :
    Function.Exact Φ.characterToRayDivisor (Φ.rayChartDivisorToPicard R hΦ) := by
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := R) hΦ
  let j := zeroChart
  intro a
  rw [rayChartDivisorToPicard, AddMonoidHom.comp_apply, ← AddMonoidHom.mem_ker,
    ker_weilToLineBundleClassHom, WeilDivisor.OrderSystem.mem_principalSubgroup]
  constructor
  · rintro ⟨f, hf⟩
    have hzero (y : CodimensionOnePoint 𝕋) :
        (𝕋).ord (j.functionFieldMap (f.toMul : (𝒳).functionField)) y.val = 0 := by
      rw [ord_functionFieldMap j, ← CodimensionOnePoint.coe_mapOfIsOpenImmersion j,
        ← orderAt_apply, ← WeilDivisor.OrderSystem.ofScheme_ord,
        ← WeilDivisor.OrderSystem.coeff_principalDivisor, hf]
      apply Φ.coeff_rayChartDivisorToWeilDivisor_of_notMem_range R hΦ
      rw [Φ.range_rayBoundaryChartPoint (R := R) hΦ (Φ.bot_mem h₀.some.property)]
      exact fun hy ↦ hy ⟨y, CodimensionOnePoint.coe_mapOfIsOpenImmersion j y |>.symm⟩
    obtain ⟨c, m, hfm⟩ := Φ.exists_eq_unit_mul_functionFieldCharacter R f.toMul hzero
    refine ⟨m, funext fun ρ ↦ ?_⟩
    have hρ := congrArg (fun D ↦ WeilDivisor.coeff D (Φ.rayBoundaryChartPoint (R := R) hΦ ρ)) hf
    rw [WeilDivisor.OrderSystem.coeff_principalDivisor, WeilDivisor.OrderSystem.ofScheme_ord,
      orderAt_apply, Φ.coeff_rayChartDivisorToWeilDivisor R hΦ,
      hfm, Φ.ord_rayBoundaryChartPoint_mul_character R hΦ ρ c m] at hρ
    simpa only [characterToRayDivisor_apply] using hρ
  · rintro ⟨m, rfl⟩
    exact ⟨Additive.ofMul ((Φ.functionFieldCharacter R).toHomUnits (ofAdd m)),
      (Φ.rayChartDivisorToWeilDivisor_characterToRayDivisor R hΦ m).symm⟩

end Principal

/-- The Picard group is the quotient of the ray coefficients by principal character divisors. -/
def rayDivisorQuotientEquivPicard (hΦ : Φ.IsRegular) :
    ((Φ.Ray → ℤ) ⧸ Φ.characterToRayDivisor.toIntLinearMap.range) ≃ₗ[ℤ]
      Additive (LineBundleClass (Φ.finiteFanScheme R)) := by
  let f := Φ.characterToRayDivisor.toIntLinearMap
  let g := (Φ.rayChartDivisorToPicard R hΦ).toIntLinearMap
  have hex : Function.Exact f g := by
    simpa only [f, g, AddMonoidHom.coe_toIntLinearMap] using
      Φ.exact_characterToRayDivisor_rayChartDivisorToPicard R hΦ
  have hg : Function.Surjective g := by
    simpa only [g, AddMonoidHom.coe_toIntLinearMap] using Φ.rayChartDivisorToPicard_surjective R hΦ
  exact (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hex).symm).trans
    (g.quotKerEquivOfSurjective hg)

/-- A ray coefficient vector represents the class of its boundary divisor. -/
theorem rayDivisorQuotientEquivPicard_mk (hΦ : Φ.IsRegular) (a : Φ.Ray → ℤ) :
    Φ.rayDivisorQuotientEquivPicard R hΦ (Submodule.Quotient.mk a) =
      Φ.rayChartDivisorToPicard R hΦ a := by
  rw [rayDivisorQuotientEquivPicard, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ a

end TauCeti.Toric.Fan
