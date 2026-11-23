/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Charge
public import QPainleve.Geometry.Toric.Fan.Picard.ChargeKernel
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

/-!
# Charge transport in the Picard change of marking

The marked Picard equivalence for an elementary transformation identifies the boundary
quotients by the dual of the integral exponent change. In the quotient, the fiber class
contributes its ray coefficient to each center on that ray. Dualizing recovers the charge
transport on the boundary orthogonal complements whenever the marked Picard equivalence
is an intersection isometry.

The geometric mutation and its charge comparison appear in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, Theorems 5.5 and 5.6.
-/

public noncomputable section

open LinearMap (BilinForm range)
open Module (Basis Dual)
open PointedCone QPainleve.Cluster
open TauCeti.AlgebraicGeometry (LineBundleClass)
open scoped Int

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (k : ι) [DecidableEq ι]
  (hOpposite : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator (s k)
local notation "hv" => IsPrimitiveGenerator.ne_zero (Ray.isPrimitiveGenerator (s k))
local notation "hpos" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Φ'" => Fan.mutationFan Φ b hv hpos hOpposite
local notation "r" => Fan.mutationFanRayEquiv Φ b hv hpos hOpposite
local notation "s'" => Fan.mutationFanCenterRays Φ b s k hOpposite
local notation "ω" => b.detDualEquiv.toLinearMap
local notation "mark" Ψ:arg => (Additive (LineBundleClass (Fan.algebraicRealization Ψ)) × (ι → ℤ))

variable (hΦ : Φ.IsRegular)

local notation "hΦ'" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hpos hOpposite) hΦ
local notation "I" => mutationPicardEquiv b s k hOpposite hΦ

private theorem map_range_markedBoundaryMap :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    (range (markedBoundaryMap hΦ' s')).map (LinearEquiv.toLinearMap I) =
      range (markedBoundaryMap hΦ s) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  let e := LinearEquiv.funCongrLeft ℤ ℤ r
  have h : LinearMap.comp (LinearEquiv.toLinearMap I) (markedBoundaryMap hΦ' s') =
      (markedBoundaryMap hΦ s).comp e.toLinearMap :=
    LinearMap.ext (mutationPicardEquiv_markedBoundaryMap b s k hOpposite hΦ)
  rw [← LinearMap.range_comp, h, e.range_comp]

/-- The marked Picard equivalence descends to the quotient by the strict-transform
boundary classes. -/
def mutationBoundaryQuotientEquiv :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    (mark Φ' ⧸ range (markedBoundaryMap hΦ' s')) ≃ₗ[ℤ]
      (mark Φ ⧸ range (markedBoundaryMap hΦ s)) :=
  Submodule.Quotient.equiv _ _ I (map_range_markedBoundaryMap b s k hOpposite hΦ)

/-- The boundary quotient map takes a representative to its marked Picard transform. -/
@[simp]
theorem mutationBoundaryQuotientEquiv_apply_mk (z : mark Φ') :
    mutationBoundaryQuotientEquiv b s k hOpposite hΦ (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (I z) :=
  (rfl)

variable [Fintype ι]

local notation "ε" => chargeExchangeMatrix ω (rayChargeMap s)
local notation "T" => chargeMutationEquiv ε k
local notation "q" => boundaryQuotientEquivDualChargeCokernel hΦ s
local notation "q'" => boundaryQuotientEquivDualChargeCokernel hΦ' s'

/-- In dual-charge coordinates, the Picard map on boundary quotients precomposes
representatives with the exponent change. The fixed-matrix exponent change is involutive,
so it gives the inverse basis change used in this dual formula. -/
theorem mutationBoundaryQuotientEquiv_apply_dual (φ : Dual ℤ (ι → ℤ)) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    mutationBoundaryQuotientEquiv b s k hOpposite hΦ ((q').symm (Submodule.Quotient.mk φ)) =
      (q).symm (Submodule.Quotient.mk ((T).dualMap φ)) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  let a : Φ.Ray → ℤ := fun ρ ↦ max (b.det ![ρ.primitiveGenerator, v]) 0
  let u : ι → ℤ := fun j ↦ φ (Pi.single j 1)
  rw [boundaryQuotientEquivDualChargeCokernel_symm_apply_mk,
    boundaryQuotientEquivDualChargeCokernel_symm_apply_mk,
    mutationBoundaryQuotientEquiv_apply_mk]
  have he : (fun j ↦ ((T).dualMap φ) (Pi.single j 1)) =
      u - (2 * u k) • Pi.single k 1 + fun j ↦ u k * a (s j) := by
    funext j
    simp only [LinearEquiv.dualMap_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = k
    · subst j
      simp [u, a, ← Basis.detDualEquiv_apply, Basis.detDualEquiv_self]
      ring
    · have ha : (-ε k j)⁺ = a (s j) := by
        simp only [chargeExchangeMatrix_apply, rayChargeMap_single, LinearEquiv.coe_coe, a]
        rw [← b.detDualEquiv_swap, Basis.detDualEquiv_apply]
        rfl
      rw [chargeMutationEquiv_single_of_ne ε k hj, map_add, map_smul, ha]
      simp [u, Pi.single_eq_of_ne hj, mul_comm]
  rw [he]
  have hi := mutationPicardEquiv_apply_rayDivisor b s k hOpposite hΦ 0 u
  have hz : (0 : (Φ').Ray → ℤ) ∘ r = 0 := (rfl)
  simp only [map_zero, hz, Pi.zero_apply, add_zero, zero_add, mutationFiberClass_eq] at hi
  rw [hi]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨u k • a, ?_⟩
  rw [markedBoundaryMap_apply, map_zsmul]
  refine Prod.ext (by simp [a]) ?_
  funext j
  simp [Pi.smul_apply, sub_eq_add_neg]
  ring

/-- The charge-kernel equivalence for toric mutation, from the mutated fan to the original fan. -/
def mutationFanChargeKernelEquiv :
    (rayChargeMap s').ker ≃ₗ[ℤ] (rayChargeMap s).ker :=
  (LinearEquiv.ofEq _ _
    (congrArg LinearMap.ker (rayChargeMap_mutationFanCenterRays b s k hOpposite))).trans
      (chargeKernelMutation ω (rayChargeMap s) k)

/-- On exponents the toric charge-kernel equivalence is the cluster exponent change. -/
@[simp]
theorem coe_mutationFanChargeKernelEquiv_apply (x : (rayChargeMap s').ker) :
    (mutationFanChargeKernelEquiv b s k hOpposite x : ι → ℤ) = T (x : ι → ℤ) := by
  rw [mutationFanChargeKernelEquiv, LinearEquiv.trans_apply, coe_chargeKernelMutation_apply,
    LinearEquiv.coe_ofEq_apply]

variable
  (B : BilinForm ℤ (Additive (LineBundleClass Φ.algebraicRealization) × (ι → ℤ)))
  (B' : BilinForm ℤ (Additive (LineBundleClass
    (Φ.mutationFan b (IsPrimitiveGenerator.ne_zero (Ray.isPrimitiveGenerator (s k)))
      (Ray.hull_primitiveGenerator_mem (s k)) hOpposite).algebraicRealization) × (ι → ℤ)))
  [LinearMap.IsPerfPair B] [LinearMap.IsPerfPair B']

local notation "ι₀" => LinearEquiv.symm (boundaryOrthogonalEquivChargeKernel hΦ s B)
local notation "ι₁" => LinearEquiv.symm (boundaryOrthogonalEquivChargeKernel hΦ' s' B')
local notation "K" => mutationFanChargeKernelEquiv b s k hOpposite

/-- The Picard change of marking and charge transport respect evaluation via the perfect
pairings on the markings. This is the dual comparison before identifying Picard mutation
with an isometry. -/
theorem mutationPicardEquiv_pairing_chargeKernel (x : (rayChargeMap s').ker) (z : mark Φ') :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    B (I z) (ι₀ (K x)) = B' z (ι₁ x) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _ (q' (Submodule.Quotient.mk z))
  have hz : (q').symm (Submodule.Quotient.mk φ) = Submodule.Quotient.mk z :=
    (LinearEquiv.symm_apply_eq _).mpr hφ
  have hIz : q (Submodule.Quotient.mk (I z)) = Submodule.Quotient.mk ((T).dualMap φ) := by
    rw [← mutationBoundaryQuotientEquiv_apply_mk b s k hOpposite hΦ, ← hz,
      mutationBoundaryQuotientEquiv_apply_dual, LinearEquiv.apply_symm_apply]
  rw [boundaryOrthogonalEquivChargeKernel_symm_pairing hΦ s B _ _ _ hIz,
    boundaryOrthogonalEquivChargeKernel_symm_pairing hΦ' s' B' _ _ _ hφ.symm,
    LinearEquiv.dualMap_apply, coe_mutationFanChargeKernelEquiv_apply]
  -- The right mutation factor is used for both directions of the fixed-matrix basis change.
  have hT (y : ι → ℤ) : (T).symm y = T y := (rfl)
  rw [← hT, LinearEquiv.symm_apply_apply]

/-- An intersection isometry having the marked mutation formulas acts on boundary
orthogonal classes by the integral cluster charge transport. -/
theorem mutationPicardEquiv_boundaryOrthogonalEquivChargeKernel_symm
    (hI : ∀ y z : mark Φ', B (I y) (I z) = B' y z) (x : (rayChargeMap s').ker) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
    I (ι₁ x : mark Φ') = (ι₀ (K x) : mark Φ) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Φ').cones := ⟨(r (s k)).toCone⟩
  apply (LinearMap.IsPerfPair.bijective_right B).injective
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := (I).surjective y
  rw [LinearMap.flip_apply, LinearMap.flip_apply, hI]
  exact (mutationPicardEquiv_pairing_chargeKernel b s k hOpposite hΦ B B' x z).symm

end TauCeti.Toric.Fan
