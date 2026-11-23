/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

import Mathlib.Tactic.Module

/-!
# Elementary transformation of ruling classes

The inverse Picard marking computes the new moving-class coordinates. For
`a F + b S` with exceptional coefficient `-m`, the new fiber coefficient is
`a + b - m` for a center on the chosen section and `a - m` for a center on the
opposite section. The new exceptional coefficient is `-(b - m)` in both cases.

These are the class formulas in [Lutz's appendix to Hacking and Keating][HKL],
Lemma 8.9. The toric calculation works for both opposite sections of any regular
rank-two fan to which the mutation applies.

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open LinearMap PointedCone
open TauCeti.AlgebraicGeometry (LineBundleClass)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  (s : ι → Φ.Ray) (k : ι)
  (hOpp : hull ℝ {i (-(s k).primitiveGenerator)} ∈ Φ.cones) (hΦ : Φ.IsRegular)

local notation "v" => Ray.primitiveGenerator (s k)
local notation "q" => Ray.ofPrimitiveGenerator (IsPrimitive.neg (IsPrimitiveGenerator.isPrimitive
  (Ray.isPrimitiveGenerator (s k)))) hOpp
local notation "hv" => Ray.primitiveGenerator_ne_zero (s k)
local notation "hp" => Ray.hull_primitiveGenerator_mem (s k)
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "I" => mutationPicardEquiv b s k hOpp hΦ
local notation "F" => mutationFiberClass b (s k) hΦ
local notation "F'" => mutationFiberClass b (r (s k)) hΨ

private theorem det_mutationFanRayEquiv (ρ : Φ.Ray) :
    b.det ![(r ρ).primitiveGenerator, v] = b.det ![ρ.primitiveGenerator, v] := by
  rw [mutationFanRayEquiv_primitiveGenerator, ← b.detDualEquiv_apply, b.detDualEquiv_swap,
    map_add, map_zsmul, b.detDualEquiv_self, smul_zero, add_zero,
    ← b.detDualEquiv_swap, b.detDualEquiv_apply]

private theorem mutationFanRayEquiv_primitiveGenerator_pivot :
    (r (s k)).primitiveGenerator = v := by
  rw [mutationFanRayEquiv_primitiveGenerator, ← b.detDualEquiv_apply, b.detDualEquiv_self]
  simp

variable [DecidableEq ι]

/-- The ruling fiber class is preserved by the Picard change of marking. The
two identified rays in the kernel of the ruling character make no exceptional
contribution. -/
@[simp]
theorem mutationPicardEquiv_fiber :
    I (F', 0) = (F, 0) := by
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Ψ).cones := ⟨(r (s k)).toCone⟩
  let a : (Ψ).Ray → ℤ := fun ρ ↦ max (b.det ![ρ.primitiveGenerator, (r (s k)).primitiveGenerator]) 0
  have ha (ρ : Φ.Ray) : a (r ρ) = max (b.det ![ρ.primitiveGenerator, v]) 0 := by
    dsimp only [a]
    rw [mutationFanRayEquiv_primitiveGenerator_pivot, det_mutationFanRayEquiv]
  have hpiv : a (r (s k)) = 0 := by
    rw [ha, ← b.detDualEquiv_apply, b.detDualEquiv_self, max_self]
  have hopp : a (r q) = 0 := by
    rw [ha, Ray.primitiveGenerator_ofPrimitiveGenerator, ← b.detDualEquiv_apply]
    simp only [map_neg, LinearMap.neg_apply, b.detDualEquiv_self, neg_zero, max_self]
  have hcomp : a ∘ r = fun ρ ↦ max (b.det ![ρ.primitiveGenerator, v]) 0 := funext ha
  rw [mutationFiberClass_eq, mutationPicardEquiv_apply_rayDivisor _ _ _ _ _ a 0,
    hcomp, hpiv, hopp, mutationFiberClass_eq]
  simp

private theorem mutationPicardEquiv_section (onSection : Bool) :
    let ρ := if onSection then s k else q
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Ψ).cones := ⟨(r (s k)).toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    letI := (Ψ).uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
    I (Additive.ofMul (LineBundleClass.primeDivisorClass ((Ψ).rayBoundaryPoint hΨ (r ρ))), 0) =
      (Additive.ofMul (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)) +
        (if onSection then 0 else F), -(Pi.single k (1 : ℤ))) := by
  classical
  intro ρ
  let : Nonempty Φ.cones := ⟨(s k).toCone⟩
  let : Nonempty (Ψ).cones := ⟨(r (s k)).toCone⟩
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := (Ψ).uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  have hn : q ≠ s k := by
    intro h
    have hg := congrArg Ray.primitiveGenerator h
    rw [Ray.primitiveGenerator_ofPrimitiveGenerator] at hg
    have hinj := (s k).isPrimitiveGenerator.isPrimitive.zsmul_left_injective
    have he : (-1 : ℤ) • v = (1 : ℤ) • v := by simpa using hg
    exact (by decide : (-1 : ℤ) ≠ 1) (hinj he)
  have h := mutationPicardEquiv_toric_single b s k hOpp hΦ ρ
  simp only [rayDivisorToPicard_single, one_smul] at h
  cases onSection <;> simpa [ρ, hn, Ne.symm hn] using h

/-- Computing the inverse Picard marking on a fiber and one of the two ruling
sections gives the class of the elementary transform. The exceptional
coefficients away from the pivot stay fixed. The new pivot coefficient is
`-d - e k` for section coefficient `d`, so a base order `m` becomes `d - m`. -/
theorem mutationPicardEquiv_symm_apply_ruling (onSection : Bool) (a d : ℤ) (e : ι → ℤ) :
    let ρ := if onSection then s k else q
    letI : Nonempty Φ.cones := ⟨(s k).toCone⟩
    letI : Nonempty (Ψ).cones := ⟨(r (s k)).toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    letI := (Ψ).uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
    let S := Additive.ofMul (LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ))
    let S' := Additive.ofMul (LineBundleClass.primeDivisorClass ((Ψ).rayBoundaryPoint hΨ (r ρ)))
    (I).symm (a • F + d • S, e) =
      ((a + e k + (if onSection then d else 0)) • F' + d • S',
        Function.update e k (-d - e k)) := by
  intro ρ S S'
  have hsection :
      I (S', 0) = (S + (if onSection then 0 else F), -Pi.single k (1 : ℤ)) :=
    mutationPicardEquiv_section b s k hOpp hΦ onSection
  have hexc (c : ι → ℤ) :
      I (0, c) = (c k • F, c - (2 * c k) • Pi.single k 1) := by
    simpa using mutationPicardEquiv_apply_rayDivisor b s k hOpp hΦ 0 c
  apply (I).injective
  rw [LinearEquiv.apply_symm_apply]
  let c := Function.update e k (-d - e k)
  let a' := a + e k + (if onSection then d else 0)
  have hsplit : ((a' • F' + d • S', c) : Additive (LineBundleClass (Ψ).algebraicRealization) ×
      (ι → ℤ)) = a' • (F', 0) + d • (S', 0) + (0, c) := by
    simp
  rw [hsplit, map_add, map_add, map_zsmul, map_zsmul, mutationPicardEquiv_fiber, hsection, hexc]
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, zero_add]
  refine (Prod.ext ?_ ?_).symm
  · have hc : c k = -d - e k := Function.update_self _ _ _
    rw [hc]
    cases onSection <;> simp only [a', Bool.false_eq_true, ↓reduceIte, add_zero] <;> module
  · funext j
    by_cases hj : j = k
    · subst j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same,
        c, Function.update_self]
      simp only [zsmul_eq_mul, Int.cast_id, mul_one]
      ring
    · simp [c, Function.update_of_ne hj, Pi.single_eq_of_ne hj]

end TauCeti.Toric.Fan
