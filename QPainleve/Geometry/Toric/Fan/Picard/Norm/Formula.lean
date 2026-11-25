/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.Picard.ChargeKernel

import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# The norm of a toric charge relation

The toric part of the norm is the signed determinant sum of the charge vectors
weighted by the relation coefficients. Across a ray, the local linear form of
a divisor changes by its degree there times the determinant character of the
ray. Summing these changes along the fan gives the norm formula. Labels on the
same ray may occur with any multiplicity.

The change of linear form uses the toric wall relation of Fulton,
*Introduction to Toric Varieties*, §5.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Chow
open LinearMap (BilinForm)

namespace TauCeti.Toric.Fan

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Φ.algebraicRealization
local notation "gen" => Ray.primitiveGenerator (Phi := Φ)
local notation "det" => b.detDualEquiv
local notation "R" => Φ.rayDivisorToPicard hΦ

private def coneCharacter (a : Φ.Ray → ℤ) (ρ τ : Φ.Ray) : N →ₗ[ℤ] ℤ :=
  a τ • det (gen ρ) - a ρ • det (gen τ)

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
private theorem coneCharacter_apply_right (a : Φ.Ray → ℤ) {ρ τ : Φ.Ray}
    (h : det (gen ρ) (gen τ) = 1) : coneCharacter b a ρ τ (gen τ) = a τ := by
  simp [coneCharacter, h, b.detDualEquiv_self]

variable [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

include hc

local notation "B" => intersectionBilinForm ℂ X

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
  rw [Φ.intersectionBilinForm_rayDivisorToPicard_single hΦ b hc a hprev hnext]
  simp only [coneCharacter, LinearMap.sub_apply, LinearMap.smul_apply, Int.zsmul_eq_mul]
  linear_combination -a ρ * h

variable [Fintype ι] {n : ℕ} [NeZero n]
  (u : ZMod n ≃ Φ.Ray)
  (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
  (s : ι → Φ.Ray)

local notation "pos(" l ")" => ZMod.val (Equiv.symm u (s l))
local notation "v(" l ")" => gen (s l)

include hu in
open Classical in
private theorem coneCharacter_prefix (a : Φ.Ray → ℤ) (x : ι → ℤ)
    (hdeg : ∀ c : Φ.Ray → ℤ, B (R c) (R a) = ∑ l, c (s l) * x l)
    (k : ι) (j : ℕ) (hj : j ≤ n) :
    let m (p : ZMod n) := coneCharacter b a (u (p - 1)) (u p)
    m (j : ZMod n) (v(k)) = m 0 (v(k)) +
      ∑ l with pos(l) < j, x l * det (v(l)) (v(k)) := by
  classical
  let m (p : ZMod n) := coneCharacter b a (u (p - 1)) (u p)
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < n := by omega
    have hw := coneCharacter_sub b hΦ hc a
      (prev := u ((j : ZMod n) - 1)) (ρ := u (j : ZMod n)) (next := u ((j : ZMod n) + 1))
      (by simpa only [sub_add_cancel] using hu ((j : ZMod n) - 1)) (hu (j : ZMod n)) (v(k))
    have hpos (l : ι) : s l = u (j : ZMod n) ↔ pos(l) = j := by
      rw [← Equiv.symm_apply_eq, ← (ZMod.val_injective n).eq_iff, ZMod.val_natCast_of_lt hj']
    have hstep : m ((j + 1 : ℕ) : ZMod n) (v(k)) - m (j : ZMod n) (v(k)) =
        ∑ l with pos(l) = j, x l * det (v(l)) (v(k)) := by
      -- The adjacent cone characters differ by the degree on the intervening ray.
      simp only [m, Nat.cast_succ, add_sub_cancel_right] at ⊢
      rw [hw, hdeg, Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : s l = u (j : ZMod n)
      · rw [ite_eq_left ((hpos l).mp hl), hl, Pi.single_eq_same, one_mul]
      · rw [ite_eq_right ((hpos l).not.mp hl), Pi.single_eq_of_ne hl, zero_mul, zero_mul]
    have hsum : (∑ l with pos(l) < j + 1, x l * det (v(l)) (v(k))) =
        (∑ l with pos(l) < j, x l * det (v(l)) (v(k))) +
        ∑ l with pos(l) = j, x l * det (v(l)) (v(k)) := by
      rw [← Finset.sum_union (by grind [Finset.disjoint_left])]
      apply Finset.sum_congr _ fun _ _ ↦ rfl
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hind := ih (by omega)
    dsimp only [m] at hstep
    dsimp only at hind ⊢
    rw [hsum, ← add_assoc, ← hind]
    exact sub_eq_iff_eq_add.mp hstep |>.trans (add_comm _ _)

include hu in
open Classical in
private theorem toric_square_eq_sum_det (x : ι → ℤ) (a : Φ.Ray → ℤ)
    (hdeg : ∀ c : Φ.Ray → ℤ, B (R c) (R a) = ∑ l, c (s l) * x l) :
    B (R a) (R a) = ∑ k, ∑ l with pos(l) < pos(k), x l * det (v(l)) (v(k)) * x k := by
  let m₀ := coneCharacter b a (u (-1)) (u 0)
  let c := Φ.characterToRayDivisor m₀.toAddMonoidHom
  have hzero : R c = 0 :=
    (Φ.exact_characterToRayDivisor_rayDivisorToPicard hΦ c).mpr ⟨_, rfl⟩
  have hprincipal : ∑ k, c (s k) * x k = 0 := by
    rw [← hdeg, hzero, map_zero, LinearMap.zero_apply]
  have hcoeff (k : ι) : a (s k) = c (s k) +
      ∑ l with pos(l) < pos(k), x l * det (v(l)) (v(k)) := by
    have h := coneCharacter_prefix b hΦ hc u hu s a x hdeg k (pos(k)) (ZMod.val_lt _).le
    dsimp only at h
    rw [ZMod.natCast_zmod_val, u.apply_symm_apply] at h
    have hdet : det (gen (u (u.symm (s k) - 1))) (v(k)) = 1 := by
      simpa only [sub_add_cancel, u.apply_symm_apply] using (hu (u.symm (s k) - 1)).1
    rw [coneCharacter_apply_right b a hdet] at h
    simpa only [c, m₀, characterToRayDivisor_apply, LinearMap.toAddMonoidHom_coe, sub_zero,
      zero_sub] using h
  simp only [hdeg a, hcoeff, add_mul, Finset.sum_add_distrib, hprincipal, zero_add, Finset.sum_mul]

local notation "Q" => BilinForm.prod B (-(dotProductBilin ℤ ℤ : BilinForm ℤ (ι → ℤ)))

omit [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

local notation "Surface" =>
  SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))

include hu in
open Classical in
/-- The norm in an internal blowup marking is the negative sum of the squared exceptional
coefficients minus the determinant sum over distinct rays in clockwise order. The cyclic
numbering is positive, so the clockwise sum pairs each label k with the labels l on rays
of smaller index. Labels on the same ray have zero determinant. -/
theorem boundary_orthogonal_norm_eq_sum_det :
    let _ : Surface := by
      rw [Φ.algebraicRealization_over]
      have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    ∀ y : BilinForm.orthogonal Q (LinearMap.range (markedBoundaryMap hΦ s)),
      (Q) y.val y.val = -(∑ k, (y.val.2 k) ^ 2) -
        ∑ k, ∑ l with pos(l) < pos(k), det (v(k)) (v(l)) * y.val.2 k * y.val.2 l := by
  intro _ y
  obtain ⟨a, ha⟩ := Φ.rayDivisorToPicard_surjective hΦ y.val.1
  have hdeg (c : Φ.Ray → ℤ) : B (R c) (R a) = ∑ l, c (s l) * (-y.val.2 l) := by
    rw [ha]
    exact markedBoundary_orthogonal_fst_pairing hΦ s B y c
  have h := toric_square_eq_sum_det b hΦ hc u hu s (-y.val.2) a hdeg
  rw [ha] at h
  have htoric : B y.val.1 y.val.1 =
      -(∑ k, ∑ l with pos(l) < pos(k), det (v(k)) (v(l)) * y.val.2 k * y.val.2 l) := by
    rw [h, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [b.detDualEquiv_swap (v(l)) (v(k))]
    simp only [Pi.neg_apply]
    ring
  simp only [BilinForm.prod_apply, LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct,
    ← pow_two, htoric]
  abel

end TauCeti.Toric.Fan
