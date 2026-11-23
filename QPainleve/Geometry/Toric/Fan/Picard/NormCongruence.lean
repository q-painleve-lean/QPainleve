/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Picard.ChargeKernel

import Mathlib.Algebra.BigOperators.ModEq
import QPainleve.Geometry.Toric.Fan.CyclicOrder
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# The norm congruence for toric blowup markings

The square of a boundary-orthogonal class is congruent to the negative sum of
the squares of its exceptional coordinates modulo any common divisor of the
charge determinants. The toric contribution vanishes modulo this divisor:
across a ray the local linear forms of a divisor differ by its degree there
times the determinant character of the ray. On the charge rays these changes
vanish modulo the divisor.

The wall relation is the toric intersection formula in Fulton, *Introduction
to Toric Varieties*, §5.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open TauCeti.AlgebraicGeometry.Chow
open LinearMap (BilinForm)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Φ.algebraicRealization
local notation "gen" => Ray.primitiveGenerator (Φ := Φ)
local notation "det" => b.detDualEquiv
local notation "R" => Φ.rayDivisorToPicard hΦ

private def coneCharacter (a : Φ.Ray → ℤ) (ρ τ : Φ.Ray) : N →ₗ[ℤ] ℤ :=
  a τ • det (gen ρ) - a ρ • det (gen τ)

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
private theorem coneCharacter_apply_left (a : Φ.Ray → ℤ) {ρ τ : Φ.Ray}
    (h : det (gen ρ) (gen τ) = 1) : coneCharacter b a ρ τ (gen ρ) = a ρ := by
  have hs := b.detDualEquiv_swap (gen τ) (gen ρ)
  simp [coneCharacter, hs, h, b.detDualEquiv_self]

variable [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

include hc

local notation "B" => intersectionBilinForm ℂ X

open Classical in
private theorem rayDegree_eq (a : Φ.Ray → ℤ) {prev ρ next : Φ.Ray}
    (hprev : det (gen prev) (gen ρ) = 1 ∧ ∃ σ : Φ.cones, prev.toCone ≤ σ ∧ ρ.toCone ≤ σ)
    (hnext : det (gen ρ) (gen next) = 1 ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ) :
    B (R (Pi.single ρ 1)) (R a) =
      a prev + Φ.rayBoundarySelfIntersection hΦ ρ * a ρ + a next := by
  let := Fintype.ofFinite Φ.Ray
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hρprev : ρ ≠ prev := by
    intro he
    have hd := hprev.1
    rw [← he, b.detDualEquiv_self] at hd
    omega
  have hρnext : ρ ≠ next := by
    intro he
    have hd := hnext.1
    rw [← he, b.detDualEquiv_self] at hd
    omega
  have hpq : prev ≠ next := by
    intro he
    have hd := hprev.1
    rw [he, b.detDualEquiv_swap, hnext.1] at hd
    omega
  have hneigh := ray_neighbors_iff_of_det b hΦ hc hprev hnext
  rw [Φ.rayDivisorToPicard_single, Φ.rayDivisorToPicard_apply]
  simp only [one_smul, map_sum, map_smul, Int.zsmul_eq_mul]
  calc
    _ = ∑ τ, ((if τ = prev then a τ else 0) +
        (if τ = ρ then Φ.rayBoundarySelfIntersection hΦ ρ * a τ else 0) +
        (if τ = next then a τ else 0)) := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul]
      by_cases h : τ = ρ
      · subst τ
        simp [hρprev, hρnext, Φ.rayBoundarySelfIntersection_def, mul_comm]
      · have hne : ρ ≠ τ := Ne.symm h
        rw [Φ.classIntersectionNumber_rayBoundaryPoint hΦ hN hne]
        have hi : (∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔ τ = prev ∨ τ = next :=
          (and_iff_right hne).symm.trans (hneigh τ)
        simp only [hi, ite_eq_right h, add_zero]
        by_cases hp : τ = prev
        · subst τ
          simp [hpq]
        · by_cases hq : τ = next <;> simp [hp, hq, hpq.symm]
    _ = _ := by simp [Finset.sum_add_distrib]

open Classical in
private theorem coneCharacter_sub (a : Φ.Ray → ℤ) {prev ρ next : Φ.Ray}
    (hprev : det (gen prev) (gen ρ) = 1 ∧ ∃ σ : Φ.cones, prev.toCone ≤ σ ∧ ρ.toCone ≤ σ)
    (hnext : det (gen ρ) (gen next) = 1 ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ)
    (v : N) :
    coneCharacter b a ρ next v - coneCharacter b a prev ρ v =
      B (R (Pi.single ρ 1)) (R a) * det (gen ρ) v := by
  have hw := primitiveGenerator_add_selfIntersection_smul_add_eq_zero b hΦ hc hprev hnext
  have h := congrArg (fun u ↦ det u v) hw
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Int.zsmul_eq_mul,
    LinearMap.zero_apply, map_zero] at h
  rw [rayDegree_eq b hΦ hc a hprev hnext]
  simp only [coneCharacter, LinearMap.sub_apply, LinearMap.smul_apply, Int.zsmul_eq_mul]
  linear_combination -a ρ * h

open Classical in
private theorem dvd_toric_square [Fintype ι] (s : ι → Φ.Ray) (x : ι → ℤ) (a : Φ.Ray → ℤ)
    (hdeg : ∀ c : Φ.Ray → ℤ, B (R c) (R a) = ∑ j, c (s j) * x j)
    {d : ℤ} (hd : ∀ j k, d ∣ det (gen (s j)) (gen (s k))) :
    d ∣ B (R a) (R a) := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp [hdeg]
  | inr h =>
    let j₀ := Classical.choice h
    have : Nonempty Φ.Ray := ⟨s j₀⟩
    have : NeZero (Nat.card Φ.Ray) := ⟨Nat.card_pos.ne'⟩
    obtain ⟨u, _, hu⟩ := (existsUnique_cyclicRayNumbering b hΦ hc (s j₀)).exists
    -- Transport the local characters around the ray cycle modulo the common divisor.
    let m (j : ZMod (Nat.card Φ.Ray)) := coneCharacter b a (u j) (u (j + 1))
    have hstep (j : ZMod (Nat.card Φ.Ray)) (k : ι) :
        m (j + 1) (gen (s k)) ≡ m j (gen (s k)) [ZMOD d] := by
      apply Int.modEq_iff_dvd.mpr
      rw [← neg_sub, Int.dvd_neg]
      rw [coneCharacter_sub b hΦ hc a (hu j) (hu (j + 1)), hdeg, Finset.sum_mul]
      apply Finset.dvd_sum
      intro l _
      by_cases hl : s l = u (j + 1)
      · rw [← hl]
        exact dvd_mul_of_dvd_right (hd l k) _
      · simp [Pi.single_eq_of_ne hl]
    have hconst (k : ι) (j : ZMod (Nat.card Φ.Ray)) :
        m j (gen (s k)) ≡ m 0 (gen (s k)) [ZMOD d] := by
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective j
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ]; exact (hstep n k).trans ih
    have hcoeff (k : ι) : a (s k) ≡ m 0 (gen (s k)) [ZMOD d] := by
      obtain ⟨j, hj⟩ := u.surjective (s k)
      have hj' : m j (gen (s k)) = a (s k) := by
        rw [← hj]
        exact coneCharacter_apply_left b a (hu j).1
      rw [← hj']
      exact hconst k j
    -- The common character represents a principal divisor, so its pairing is zero.
    let c := Φ.characterToRayDivisor (m 0).toAddMonoidHom
    have hzero : R c = 0 :=
      (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ c).mpr ⟨_, rfl⟩
    have heq : ∑ j, c (s j) * x j = 0 := by rw [← hdeg, hzero, map_zero, LinearMap.zero_apply]
    rw [hdeg, ← Int.modEq_zero_iff_dvd, ← heq]
    exact Int.ModEq.sum fun k _ ↦ by
      simp only [c, characterToRayDivisor_apply]
      exact (hcoeff k).mul_right (x k)

variable [Fintype ι]

local notation "Q" => BilinForm.prod B (-(dotProductBilin ℤ ℤ : BilinForm ℤ (ι → ℤ)))

private theorem marked_norm_modEq (s : ι → Φ.Ray)
    (y : BilinForm.orthogonal Q (LinearMap.range (markedBoundaryMap hΦ s)))
    {d : ℤ} (hd : ∀ j k, d ∣ det (gen (s j)) (gen (s k))) :
    (Q) y.val y.val ≡ -∑ j, (y.val.2 j) ^ 2 [ZMOD d] := by
  obtain ⟨a, ha⟩ := Φ.rayDivisorToPicard_surjective hΦ y.val.1
  have hdeg (c : Φ.Ray → ℤ) : B (R c) (R a) = ∑ j, c (s j) * (-y.val.2 j) := by
    have hz := BilinForm.mem_orthogonal_iff.mp y.property (markedBoundaryMap hΦ s c)
      (LinearMap.mem_range_self _ c)
    simp only [markedBoundaryMap_apply, BilinForm.prod_apply, LinearMap.neg_apply,
      dotProductBilin_apply_apply, dotProduct,
      neg_mul, Finset.sum_neg_distrib, neg_neg, ← ha] at hz
    simpa only [mul_neg, Finset.sum_neg_distrib] using eq_neg_of_add_eq_zero_left hz
  have hdiv := dvd_toric_square b hΦ hc s (-y.val.2) a hdeg hd
  rw [ha] at hdiv
  simp only [BilinForm.prod_apply, LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct,
    ← pow_two]
  simpa only [zero_add] using (Int.modEq_zero_iff_dvd.mpr hdiv).add_right (-∑ j, y.val.2 j ^ 2)

omit [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

local notation "Surface" =>
  SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))

/-- The norm of a boundary-orthogonal class in an ordered internal blowup marking is
congruent to the negative sum of the squares of its exceptional coordinates modulo any
common divisor of the pairwise charge determinants. The result allows repeated rays
and charge images of any rank. -/
theorem boundaryOrthogonal_norm_modEq (s : ι → Φ.Ray) :
    let _ : Surface := by
      rw [Φ.algebraicRealization_over]
      have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    ∀ (y : BilinForm.orthogonal Q (LinearMap.range (markedBoundaryMap hΦ s)))
      {d : ℤ}, (∀ j k, d ∣ det (gen (s j)) (gen (s k))) →
        (Q) y.val y.val ≡ -∑ j, (y.val.2 j) ^ 2 [ZMOD d] := by
  intro _ y d hd
  exact marked_norm_modEq b hΦ hc s y hd

/-- In charge-kernel coordinates the square of a boundary-orthogonal class is congruent to
the negative sum of squares of the relation coefficients modulo any common divisor of
the pairwise charge determinants. -/
theorem boundaryOrthogonalEquivChargeKernel_symm_norm_modEq (s : ι → Φ.Ray) :
    let _ : Surface := by
      rw [Φ.algebraicRealization_over]
      have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    ∀ [LinearMap.IsPerfPair Q] (x : (rayChargeMap s).ker) {d : ℤ},
      (∀ j k, d ∣ det (gen (s j)) (gen (s k))) →
        let y := (boundaryOrthogonalEquivChargeKernel hΦ s Q).symm x
        (Q) y.val y.val ≡ -∑ j, x.val j ^ 2 [ZMOD d] := by
  intro _ _ x d hd
  simpa only [boundaryOrthogonalEquivChargeKernel_symm_snd, Pi.neg_apply, neg_sq] using
    marked_norm_modEq b hΦ hc s ((boundaryOrthogonalEquivChargeKernel hΦ s Q).symm x) hd

end TauCeti.Toric.Fan
