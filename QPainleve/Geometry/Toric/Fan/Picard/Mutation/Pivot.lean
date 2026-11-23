/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.Geometry.Toric.Fan.Mutation.Pivot
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.LinearAlgebra.Determinant.Dual
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# The pivot exceptional class under toric mutation

The pullback of the new exceptional class over the ruling torus is the class of the
total pivot fiber minus the original exceptional class. The pivot fiber has the
same class as the boundary fiber in the toric divisor presentation, so the formula
is the exceptional-generator formula in the marked Picard comparison.

See Gross, Hacking and Keel, [*Birational geometry of cluster algebras*,
§3.1 and the proof of Theorem 5.6](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone Scheme
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "v" => Ray.primitiveGenerator ρ
local notation "m" => LinearMap.toAddMonoidHom (Basis.detDualEquiv b v)
local notation "hs" => detCharacter_nonneg_or_nonpos Φ b
  (Ray.primitiveGenerator_ne_zero ρ) (Ray.hull_primitiveGenerator_mem ρ) hOpp
local notation "r" => Φ.characterRuling m hs
local notation "j" => pullback.fst r projectiveLineTorusι
local notation "I₀" => Ray.mutationPivotSourceIdeal b ρ hOpp c
local notation "I₁" => Ray.mutationPivotTargetIdeal b ρ hOpp c
local notation "π" => IdealSheafData.blowupToBase I₀ ≫ j
local notation "E" => Ray.mutationPivotIso b ρ hOpp c
local notation "p" =>
  projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (Units.val ((-1 : ℂˣ) * c⁻¹))

private theorem pivotCharacter_ne_zero :
    m ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := ρ.surjective_detCharacter b 1
  have he : m x = 1 := hx
  simp [h] at he

private theorem pivotPoint_over :
    p ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _ := by
  simp [projectiveLine.polynomialPoint_over]

local notation "F" => IdealSheafData.comap (Scheme.Hom.ker p) r

local notation "hF" => Φ.isEffectiveCartier_characterRuling_fiber m hs
  (pivotCharacter_ne_zero b ρ) p (pivotPoint_over c)

/-- The ray-divisor class in the marked mutation formula is the class of the actual
scheme fiber over the pivot point of the ruling. -/
theorem Ray.exists_mutationFiberClass_eq_pivotFiber (hΦ : Φ.IsRegular) :
    ∃ hCartier : (F).IsEffectiveCartier,
      (Φ.mutationFiberClass b ρ hΦ).toMul = (LineBundleClass.mk hCartier.toInvertibleSheaf)⁻¹ := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  refine ⟨hF, ?_⟩
  have hclass := Φ.toLineBundleClass_characterRuling_fiber m hs
    (pivotCharacter_ne_zero b ρ) p (pivotPoint_over c) hΦ
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
  have hmarked : Φ.mutationFiberClass b ρ hΦ =
      Additive.ofMul (LineBundleClass.mk (hF).toInvertibleSheaf)⁻¹ := by
    rw [mutationFiberClass_eq, hclass]
    symm
    apply sub_eq_zero.mp
    rw [← map_sub, hsub]
    exact (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ).apply_apply_eq_zero m
  exact congrArg Additive.toMul hmarked

/-- On the pivot blowup over the ruling torus, the opposite exceptional class pulls back
to the marked fiber class minus the source exceptional class. -/
theorem Ray.pullback_blowupExceptionalClass_mutationPivotIso (hΦ : Φ.IsRegular) :
    LineBundleClass.pullback (E).hom (I₁).blowupExceptionalClass =
      LineBundleClass.pullback π (Φ.mutationFiberClass b ρ hΦ).toMul /
        (I₀).blowupExceptionalClass := by
  obtain ⟨hFiber, hFiberClass⟩ := ρ.exists_mutationFiberClass_eq_pivotFiber b hOpp c hΦ
  let he₀ := (I₀).isEffectiveCartier_comap_blowupToBase
  let he₁ := (I₁).isEffectiveCartier_comap_blowupToBase
  let he := he₁.comap (E).hom
  have hprod : (F).comap π =
      ((I₀).comap (I₀).blowupToBase) * (((I₁).comap (I₁).blowupToBase).comap (E).hom) := by
    simpa only [Category.assoc, comap_comp] using ρ.comap_pivotFiber_mutationPivotIso b hOpp c
  have hπ : ((F).comap π).IsEffectiveCartier := hprod.symm ▸ isEffectiveCartier_mul he₀ he
  rw [hFiberClass, pullback_inv, hFiber.pullback_mk_toInvertibleSheaf hπ]
  exact (I₁).pullback_blowupExceptionalClass_eq_div_of_eq_mul (E).hom hπ he hprod

end TauCeti.Toric.Fan
