/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.Geometry.Toric.Fan.Mutation.Blowup
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.LinearAlgebra.Determinant.Dual
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# The pivot exceptional class under toric mutation

The global pivot blowup isomorphism pulls back the target exceptional class to
the class of the total pivot fiber minus the original exceptional class. The
pivot fiber has the same class as the boundary fiber in the toric divisor
presentation. The formula also holds on the restriction over the ruling torus.

See Gross, Hacking and Keel, [*Birational geometry of cluster algebras*,
§3.1 and the proof of Theorem 5.6](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone Scheme
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] {N V : Type}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : Kˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "m" => LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
local notation "hs" => detCharacter_nonneg_or_nonpos Φ b
  (Ray.primitiveGenerator_ne_zero ρ) (Ray.hull_primitiveGenerator_mem ρ) hOpp
local notation "r" => Φ.characterRuling K m hs
local notation "j" => pullback.fst r (projectiveLineTorusι K)
local notation "I₀" => Ray.mutationPivotSourceIdeal b ρ hOpp c
local notation "I₁" => Ray.mutationPivotTargetIdeal b ρ hOpp c
local notation "π" => IdealSheafData.blowupToBase I₀ ≫ j
local notation "E" => Ray.mutationPivotIso b ρ hOpp c
local notation "p" =>
  projectiveLine.polynomialPoint K (RingHom.id K) 0 (Units.val ((-1 : Kˣ) * c⁻¹))

private theorem pivotCharacter_ne_zero :
    m ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := ρ.surjective_detCharacter b 1
  have he : m x = 1 := hx
  simp [h] at he

private theorem pivotPoint_over :
    p ≫ (projectiveLine K ↘ Spec (.of K)) = 𝟙 _ := by
  simp [projectiveLine.polynomialPoint_over]

local notation "F" => IdealSheafData.comap (Scheme.Hom.ker p) r

local notation "hF" => Φ.isEffectiveCartier_characterRuling_fiber K m hs
  (pivotCharacter_ne_zero b ρ) p (pivotPoint_over K c)

/-- The ray-divisor class in the marked mutation formula is the class of the actual
scheme fiber over the pivot point of the ruling. -/
theorem Ray.exists_mutationFiberClass_eq_pivotFiber (hΦ : Φ.IsRegular) :
    ∃ hCartier : (F).IsEffectiveCartier,
      (Φ.mutationFiberClass K b ρ hΦ).toMul =
        (LineBundleClass.mk hCartier.toInvertibleSheaf)⁻¹ := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  refine ⟨hF, ?_⟩
  have hclass := Φ.toLineBundleClass_characterRuling_fiber K m hs
    (pivotCharacter_ne_zero b ρ) p (pivotPoint_over K c) hΦ
  dsimp only at hclass
  rw [IsEffectiveCartier.toLineBundleClass_toCartierDivisor] at hclass
  have hcoeff (u : Φ.Ray) : b.det ![u.primitiveGenerator, v] = -m u.primitiveGenerator := by
    rw [← Basis.detDualEquiv_apply, Basis.detDualEquiv_swap b u.primitiveGenerator v]
    rfl
  -- The marked fiber uses the opposite sign of the ruling character. The difference
  -- of the two ray divisors is principal.
  have hsub : (fun u : Φ.Ray ↦ max (m u.primitiveGenerator) 0) -
      (fun u : Φ.Ray ↦ max (b.det ![u.primitiveGenerator, v]) 0) =
        Φ.characterToRayDivisor m := by
    funext u
    simp only [Pi.sub_apply, hcoeff, characterToRayDivisor_apply, max_zero_sub_max_neg_zero_eq_self]
  have hmarked : Φ.mutationFiberClass K b ρ hΦ =
      Additive.ofMul (LineBundleClass.mk (hF).toInvertibleSheaf)⁻¹ := by
    rw [mutationFiberClass_eq, hclass]
    symm
    apply sub_eq_zero.mp
    rw [← map_sub, hsub]
    exact (Φ.exact_characterToRayDivisor_rayChartDivisorToPicard K hΦ).apply_apply_eq_zero m
  exact congrArg Additive.toMul hmarked

private theorem pullback_blowupExceptionalClass_eq_div_mutationFiber
    (hΦ : Φ.IsRegular) {X Y : Scheme} (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (g : I.blowup ⟶ J.blowup) [Flat g] (f : I.blowup ⟶ Φ.finiteFanScheme K)
    (hprod : (F).comap f =
      (I.comap I.blowupToBase) * ((J.comap J.blowupToBase).comap g)) :
    pullback g J.blowupExceptionalClass =
      pullback f (Φ.mutationFiberClass K b ρ hΦ).toMul / I.blowupExceptionalClass := by
  obtain ⟨hFiber, hFiberClass⟩ := ρ.exists_mutationFiberClass_eq_pivotFiber K b hOpp c hΦ
  let hE := J.isEffectiveCartier_comap_blowupToBase.comap g
  have hf : ((F).comap f).IsEffectiveCartier :=
    hprod.symm ▸ isEffectiveCartier_mul I.isEffectiveCartier_comap_blowupToBase hE
  rw [hFiberClass, pullback_inv, hFiber.pullback_mk_toInvertibleSheaf hf]
  exact J.pullback_blowupExceptionalClass_eq_div_of_eq_mul g hf hE hprod

/-- On the pivot blowup over the ruling torus, the opposite exceptional class pulls back
to the marked fiber class minus the source exceptional class. -/
theorem Ray.pullback_blowupExceptionalClass_mutationPivotIso (hΦ : Φ.IsRegular) :
    pullback (E).hom (I₁).blowupExceptionalClass =
      pullback π (Φ.mutationFiberClass K b ρ hΦ).toMul / (I₀).blowupExceptionalClass := by
  apply pullback_blowupExceptionalClass_eq_div_mutationFiber K b ρ hOpp c hΦ
  simpa only [Category.assoc, comap_comp] using ρ.comap_pivotFiber_mutationPivotIso b hOpp c

local notation "J₀" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J₁" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "G" => Ray.mutationBlowupIso b ρ hOpp c

/-- On the global pivot blowups, the opposite exceptional class pulls back to the
marked ruling fiber class minus the original exceptional class. -/
theorem Ray.pullback_blowupExceptionalClass_mutationBlowupIso (hΦ : Φ.IsRegular) :
    pullback (G).hom (J₁).blowupExceptionalClass =
      pullback (J₀).blowupToBase (Φ.mutationFiberClass K b ρ hΦ).toMul /
        (J₀).blowupExceptionalClass := by
  apply pullback_blowupExceptionalClass_eq_div_mutationFiber K b ρ hOpp c hΦ
  simpa only [comap_comp, Units.val_mul, Units.val_neg, Units.val_one, neg_mul, one_mul] using
    ρ.comap_pivotFiber_mutationBlowupIso b hOpp c

end TauCeti.Toric.Fan
