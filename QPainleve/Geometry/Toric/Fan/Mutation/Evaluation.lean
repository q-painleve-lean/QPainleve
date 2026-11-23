/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Evaluation
public import QPainleve.Geometry.Toric.Fan.Charge
public import QPainleve.Geometry.Toric.Fan.Mutation.Pullback
public import QPainleve.SignedClusterModularGroup.CenterMutation

/-!
# Cluster X evaluation at fixed toric centers

Specializing the Laurent mutation chart at fixed centers sends its coordinates to scaled
determinant characters. Pullback along the toric elementary transformation commutes with
this specialization and cluster X mutation. The localization inverts the pivot binomial,
so the comparison takes place on the common rational domain.

The character and charge formulas used here are those of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, (1.2), (2.9), and §3.1]
(https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry Multiplicative PointedCone
open QPainleve.Cluster TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {l : N →+ V} (Φ : Fan l) (b : Module.Basis (Fin 2) ℤ N)
  {ι : Type} [DecidableEq ι] (s : ι → Φ.Ray) (p : ι)
  (c : Multiplicative (ι → ℤ) →* ℂˣ)

local notation "u" j:arg => Ray.primitiveGenerator (Φ := Φ) (s j)
local notation "χ(" x ")" => LinearMap.toAddMonoidHom (b.detDualEquiv x)
local notation "c[" j "]" => c (ofAdd (Pi.single j 1))
local notation "K(" F ")" => Scheme.functionField (Fan.algebraicRealization F)
local notation "hΦ" => Nonempty.intro (Ray.toCone Φ (s p))

omit [DecidableEq ι] in
private theorem pivotCharacter_ne_zero : χ(u p) ≠ 0 := by
  intro h
  apply (s p).primitiveGenerator_ne_zero
  apply b.detDualEquiv.injective
  ext x
  simpa only [map_zero, LinearMap.zero_apply, LinearMap.toAddMonoidHom_coe,
    AddMonoidHom.zero_apply] using DFunLike.congr_fun h x

/-- Specialization of the localized X chart at a fixed center character. The pivot binomial
is nonzero because the pivot ray has a nonzero primitive generator. -/
def mutationChartEval :
    letI : Nonempty Φ.cones := hΦ
    XMutationChart ℂ p →ₐ[ℂ] K(Φ) := by
  let : Nonempty Φ.cones := hΦ
  refine xMutationChartEval p (fun j ↦
    Units.map (algebraMap ℂ K(Φ)).toMonoidHom c[j] * Φ.character.toHomUnits (ofAdd χ(u j))) ?_
  simpa using (Φ.one_add_mul_character_ne_zero (c[p] : ℂ)
    (pivotCharacter_ne_zero Φ b s p)).isUnit

/-- The X coordinate at a fixed center is its center parameter times its charge character. -/
@[simp]
theorem mutationChartEval_X (j : ι) :
    letI : Nonempty Φ.cones := hΦ
    Φ.mutationChartEval b s p c (algebraMap (LaurentRing ℂ ι) (XMutationChart ℂ p) (X j)) =
      algebraMap ℂ K(Φ) (c[j] : ℂ) * Φ.character (ofAdd χ(u j)) := by
  simp [mutationChartEval]

variable [Fintype ι] (hOpposite : hull ℝ {l (-(s p).primitiveGenerator)} ∈ Φ.cones)

local notation "hpos" => Ray.hull_primitiveGenerator_mem (Φ := Φ) (s p)
local notation "hv" => Ray.primitiveGenerator_ne_zero (Φ := Φ) (s p)
local notation "Ψ" => mutationFan (i := l) Φ b (v := u p) hv hpos hOpposite
local notation "s′" => mutationFanCenterRays (i := l) Φ b s p hOpposite
local notation "ω" => b.detDualEquiv.toLinearMap
local notation "ε" => chargeExchangeMatrix ω (rayChargeMap s)
local notation "a(" j ")" => (ε j p)
local notation "c′" => MonoidHom.comp c (AddMonoidHom.toMultiplicative
  (AddEquiv.toAddMonoidHom (LinearEquiv.toAddEquiv (chargeMutationEquiv ε p))))
local notation "P" =>
  (mutationComplementPullbackAlgHom (i := l) Φ b (c[p] : ℂ) (v := u p) hv hpos hOpposite :
    K(Ψ) →ₐ[ℂ] K(Φ))
local notation "M" => xMutationChartEquiv ℂ p (fun j ↦ a(j))

local notation "hΨ" => Nonempty.intro (Ray.toCone Ψ (s′ p))

local notation "X₀(" j ")" => Φ.mutationChartEval b s p c
  (xMutationChartUnitX ℂ p j : XMutationChart ℂ p)

private theorem comp_eval_unitX_self :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    P (mutationChartEval (l := l) Ψ b s′ p c′ (xMutationChartUnitX ℂ p p : XMutationChart ℂ p)) =
      (X₀(p))⁻¹ := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  have hchar : χ(-(u p)) = -χ(u p) := by
    ext x
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.neg_apply, map_neg,
      LinearMap.neg_apply]
  simp only [val_xMutationChartUnitX, mutationChartEval_X]
  rw [mutationFanCenterRays_primitiveGenerator_self,
    centerMutation_character_apply_self, map_mul, AlgHom.commutes,
    mutationComplementPullbackAlgHom_apply, mutationComplementPullback_character, hchar]
  simp only [AddMonoidHom.neg_apply, LinearMap.toAddMonoidHom_coe, b.detDualEquiv_self, neg_zero,
    zpow_zero, one_mul, Units.val_inv_eq_inv_val, map_inv₀, ofAdd_neg, map_inv, mul_inv_rev,
    mul_comm]

open scoped Int in
private theorem comp_eval_unitX_of_ne {j : ι} (hj : j ≠ p) :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    P (mutationChartEval (l := l) Ψ b s′ p c′ (xMutationChartUnitX ℂ p j : XMutationChart ℂ p)) =
      X₀(j) * X₀(p) ^ max (a(j)) 0 * (1 + X₀(p)) ^ (-a(j)) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  let n : ℤ := max (a(j)) 0
  have hω : (ω : LinearMap.BilinForm ℤ N).IsAlt := b.detDualEquiv_self
  have hcharge : (s′ j).primitiveGenerator = u j + n • u p := by
    rw [mutationFanCenterRays_primitiveGenerator_of_ne _ _ _ _ _ hj]
    simp only [n, chargeExchangeMatrix_apply, rayChargeMap_single, LinearEquiv.coe_coe,
      Module.Basis.detDualEquiv_apply]
  have hpair : χ(u j + n • u p) (u p) = a(j) := by
    simp [LinearMap.add_apply, LinearMap.smul_apply, b.detDualEquiv_self]
  have hchar : χ(u j + n • u p) = χ(u j) + n • χ(u p) := by
    ext x
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
      map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [val_xMutationChartUnitX, mutationChartEval_X]
  rw [centerMutation_character_apply_of_ne _ _ _ ℂ hω c hj,
    map_mul, AlgHom.commutes, mutationComplementPullbackAlgHom_apply,
    mutationComplementPullback_character, hcharge, hpair, hchar]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ofAdd_add, ofAdd_zsmul,
    map_zpow, n, posPart_def, mul_zpow]
  -- Treat the two pivot factors as field elements for the final rearrangement.
  generalize algebraMap ℂ K(Φ) (c[p] : ℂ) = cp,
    Φ.character (ofAdd χ(u p)) = zp
  ring

/-- The actual toric mutation pullback commutes with fixed-center X evaluation on the
whole localized Laurent chart. The target uses the mutated rays and the monomial change
of center parameters. -/
theorem mutationComplementPullback_comp_mutationChartEval :
    letI : Nonempty Φ.cones := hΦ
    letI : Nonempty (Fan.cones Ψ) := hΨ
    AlgHom.comp P (mutationChartEval (l := l) Ψ b s′ p c′) =
      (Φ.mutationChartEval b s p c).comp (AlgEquiv.toAlgHom M) := by
  let : Nonempty Φ.cones := hΦ
  let : Nonempty (Fan.cones Ψ) := hΨ
  apply Localization.algHom_ext
  apply LaurentRing.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
    ← val_xMutationChartUnitX, AlgEquiv.toAlgHom_apply]
  let evalUnits := Units.map (Φ.mutationChartEval b s p c : XMutationChart ℂ p →* K(Φ))
  by_cases hj : j = p
  · subst j
    rw [comp_eval_unitX_self]
    have h := congrArg (fun x ↦ (evalUnits x : K(Φ)))
      (map_xMutationChartUnitX_self ℂ p (fun j ↦ a(j)))
    simpa only [evalUnits, map_inv, Units.val_inv_eq_inv_val, Units.coe_map,
      MonoidHom.coe_ofClass, AlgHom.coe_toMonoidHom] using h.symm
  · rw [comp_eval_unitX_of_ne _ _ _ _ _ _ hj]
    have h := congrArg (fun x ↦ (evalUnits x : K(Φ)))
      (map_xMutationChartUnitX_of_ne ℂ p (fun j ↦ a(j)) hj)
    simpa only [evalUnits, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.coe_map, MonoidHom.coe_ofClass, AlgHom.coe_toMonoidHom, val_xMutationChartBinomial,
      map_add, map_one] using h.symm

end TauCeti.Toric.Fan
