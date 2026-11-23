/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Geometry.Toric.Fan.Charge
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary

/-!
# Tropical mutation and toric ray transport

Tropical mutation transports the orders of the specialized X coordinates from a boundary
ray to its image under the integral shear. This identifies the tropical calculation
with the orders of the actual function-field pullbacks, in the determinant convention
of Gross, Hacking and Keel, *Birational geometry of cluster algebras*, (1.4) and
the proof of Theorem 5.6.
-/

public noncomputable section

open AlgebraicGeometry Multiplicative QPainleve.Cluster
open scoped Int

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Fan i}
  (b : Module.Basis (Fin 2) ℤ N) (s : ι → Φ.Ray) (k : ι)
  (hOpposite : PointedCone.hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator (s k)
local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hRay" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => mutationFan Φ b hv hRay hOpposite
local notation "r" => mutationFanRayEquiv Φ b hv hRay hOpposite
local notation "s'" => mutationFanCenterRays Φ b s k hOpposite
local notation "ω" => Module.Basis.detDualEquiv b
local notation "ε" => chargeExchangeMatrix (LinearEquiv.toLinearMap ω) (rayChargeMap s)
local notation "B" => SkewExchangeMatrix.ofMatrix ε
  (isSkewSymmetrizer_chargeExchangeMatrix _ (b.detDualEquiv_self) _)

/-- The tropicalized boundary orders agree with the pairings of the new charges
with the sheared ray generator. -/
theorem tropical_mutate_rayPairing (ρ : Φ.Ray) :
    (Generator.mutate k).tropical (B) (fun j ↦ ω (s j).primitiveGenerator ρ.primitiveGenerator) =
      fun j ↦ ω ((s') j).primitiveGenerator ((r) ρ).primitiveGenerator := by
  funext j
  rw [mutationFanRayEquiv_primitiveGenerator, ← b.detDualEquiv_apply,
    b.detDualEquiv_swap ρ.primitiveGenerator v]
  have hs : max (-ω v ρ.primitiveGenerator) 0 = -min 0 (ω v ρ.primitiveGenerator) := by omega
  rw [hs]
  rcases eq_or_ne j k with rfl | hj
  · rw [Generator.tropical_mutate_self, mutationFanCenterRays_primitiveGenerator_self]
    simp only [map_neg, LinearMap.neg_apply, map_add, map_zsmul,
      b.detDualEquiv_self, neg_zero, smul_zero, add_zero]
  · rw [Generator.tropical_mutate_of_ne _ _ hj, SkewExchangeMatrix.matrix_ofMatrix,
      chargeExchangeMatrix_apply, rayChargeMap_single, rayChargeMap_single,
      mutationFanCenterRays_primitiveGenerator_of_ne _ _ _ _ _ hj, ← b.detDualEquiv_apply]
    simp only [LinearEquiv.coe_coe, posPart_def, map_add, map_zsmul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, b.detDualEquiv_self]
    ring

/-- The tropical mutation of the source X orders gives the orders of the geometric
pullbacks of the terminal X coordinates. Scalar center factors have order zero. -/
theorem tropical_mutate_eq_ord_rayBoundaryPoint_mutationComplementPullback
    (hΦ : Φ.IsRegular) (ρ : Φ.Ray) (c d : ι → ℂˣ) :
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Ψ).cones := ⟨((r) (s k)).toCone⟩
    ∀ j, (Generator.mutate k).tropical (B)
      (fun l ↦ Φ.algebraicRealization.ord
        (algebraMap ℂ Φ.algebraicRealization.functionField (c l : ℂ) *
          Φ.character (ofAdd (ω (s l).primitiveGenerator).toAddMonoidHom))
        (Φ.rayBoundaryPoint hΦ ρ).val) j =
      Φ.algebraicRealization.ord
        (Φ.mutationComplementPullback b (c k : ℂ) hv hRay hOpposite
          (algebraMap ℂ (Ψ).algebraicRealization.functionField (d j : ℂ) *
            (Ψ).character (ofAdd (ω ((s') j).primitiveGenerator).toAddMonoidHom)))
        (Φ.rayBoundaryPoint hΦ ρ).val := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Ψ).cones := ⟨((r) (s k)).toCone⟩
  intro j
  simp only [Φ.ord_rayBoundaryPoint_mul_character,
    Φ.ord_rayBoundaryPoint_mutationComplementPullback b (c k) hv hRay hOpposite,
    (Ψ).ord_rayBoundaryPoint_mul_character, LinearMap.toAddMonoidHom_coe]
  exact congrFun (tropical_mutate_rayPairing b s k hOpposite ρ) j

end TauCeti.Toric.Fan
