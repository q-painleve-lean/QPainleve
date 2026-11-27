/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Geometry.Toric.Fan.Charge
public import QPainleve.Geometry.Toric.Fan.Mutation.Basic

/-!
# Charges of mutated toric centers

The ray generators after an elementary transformation give the same charges as the
integral basis change used in cluster mutation. This compares the center data of the
fan construction with the exponent transport before passing to Picard groups.
See Gross, Hacking and Keel, *Birational geometry of cluster algebras*, Theorem 5.6.
-/

public noncomputable section

open Module (Basis)
open PointedCone QPainleve.Cluster
open scoped Int

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (k : ι) [DecidableEq ι]
  (hOpposite : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

/-- The charges of the mutated centers are obtained by the same integral change of basis
that transports cluster exponents. -/
theorem rayChargeMap_mutationFanCenterRays [Fintype ι] :
    rayChargeMap (Φ.mutationFanCenterRays b s k hOpposite) =
      chargeMutation b.detDualEquiv.toLinearMap (rayChargeMap s) k := by
  apply (Pi.basisFun ℤ ι).ext
  intro j
  simp only [Pi.basisFun_apply, rayChargeMap_single]
  by_cases hj : j = k
  · subst j
    rw [chargeMutation_single_self, rayChargeMap_single,
      mutationFanCenterRays_primitiveGenerator_self]
  · rw [chargeMutation_single_of_ne _ (b.detDualEquiv_self) _ hj, chargeExchangeMatrix_apply,
      rayChargeMap_single, rayChargeMap_single, mutationFanCenterRays_primitiveGenerator_of_ne
        Φ b s k hOpposite hj]
    simp only [LinearEquiv.coe_coe, Basis.detDualEquiv_apply]
    rfl

variable (Φ)

local notation "v(" j ")" => Ray.primitiveGenerator (s j)
local notation "hvₖ" => IsPrimitiveGenerator.ne_zero (Ray.isPrimitiveGenerator (s k))
local notation "h₊" => Ray.hull_primitiveGenerator_mem (s k)
local notation "s'" => Φ.mutationFanCenterRays b s k hOpposite
local notation "ρ'(" ρ ")" => Φ.mutationFanRayEquiv b hvₖ h₊ hOpposite ρ
local notation "d" => b.detDualEquiv

/-- The integer valuation row of the center characters at the sheared ray
is the tropical mutation of the original row. Only the pivot column of the
exchange matrix enters this calculation. -/
theorem tropical_mutate_eq_rayPairing_mutationFanRayEquiv (B : SkewExchangeMatrix ι)
    (hB : ∀ j, B.matrix j k = d v(j) v(k)) (ρ : Φ.Ray) :
    (Generator.mutate k).tropical B (fun j ↦ d v(j) ρ.primitiveGenerator) =
      fun j ↦ d ((s') j).primitiveGenerator (ρ'(ρ)).primitiveGenerator := by
  funext j
  by_cases hj : j = k
  · subst j
    rw [Generator.tropical_mutate_self, mutationFanCenterRays_primitiveGenerator_self,
      mutationFanRayEquiv_primitiveGenerator, map_neg, LinearMap.neg_apply, map_add, map_zsmul,
      b.detDualEquiv_self, smul_zero, add_zero]
  · rw [Generator.tropical_mutate_of_ne B _ hj, hB, mutationFanCenterRays_primitiveGenerator_of_ne
      Φ b s k hOpposite hj, mutationFanRayEquiv_primitiveGenerator]
    have hmin : min 0 (d v(k) ρ.primitiveGenerator) =
        -max (b.det ![ρ.primitiveGenerator, v(k)]) 0 := by
      rw [b.detDualEquiv_swap v(k) ρ.primitiveGenerator, b.detDualEquiv_apply]
      simpa only [neg_zero, max_comm] using
        min_neg_neg (0 : ℤ) (b.det ![ρ.primitiveGenerator, v(k)])
    rw [hmin]
    simp only [posPart_def, ← b.detDualEquiv_apply, map_add, map_zsmul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, b.detDualEquiv_self, mul_zero, add_zero]
    ring

end TauCeti.Toric.Fan
