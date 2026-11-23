/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
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
  (hOpposite : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) [Fintype ι]

/-- The charges of the mutated centers are obtained by the same integral change of basis
that transports cluster exponents. -/
theorem rayChargeMap_mutationFanCenterRays :
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

end TauCeti.Toric.Fan
