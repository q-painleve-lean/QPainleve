/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.LightCone

/-!
# Halves of the positive locus of a quadratic form

For a nondegenerate quadratic form of positive index one, a vector of positive square
selects a convex half of the positive locus by the sign of the polar pairing. Any
nonzero vector of nonnegative square pairing positively with it selects the same half.
Two vectors of nonnegative square on the same closed side pair nonnegatively.
The comparison uses Tau Ceti's `QuadraticForm.sign_polar_eq_sign_polar`.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- Two vectors of nonnegative square on the same closed side of a positive vector
have nonnegative polar pairing. -/
theorem polar_nonneg_of_nonneg_of_polar_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h x y : V} (hh : 0 < Q h) (hx : 0 ≤ Q x) (hy : 0 ≤ Q y)
    (hhx : 0 ≤ polar Q h x) (hhy : 0 ≤ polar Q h y) : 0 ≤ polar Q x y := by
  by_contra! hxy
  have hx₀ : x ≠ 0 := by rintro rfl; simp at hxy
  have hy₀ : y ≠ 0 := by rintro rfl; simp at hxy
  have ha : 0 < polar Q h y := lt_of_le_of_ne hhy fun he ↦
    hy₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh ((polar_comm Q y h).trans he.symm) hy)
  have hb : 0 < polar Q h x := lt_of_le_of_ne hhx fun he ↦
    hx₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh ((polar_comm Q x h).trans he.symm) hx)
  -- A negative pairing would make this vector positive even though it is orthogonal to h.
  let w := polar Q h y • x - polar Q h x • y
  have hw : 0 < Q w := by
    simp only [w, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.map_smul, polar_neg_right, polar_smul_left, polar_smul_right, smul_eq_mul]
    have hx' := mul_nonneg (mul_self_nonneg (polar Q h y)) hx
    have hy' := mul_nonneg (mul_self_nonneg (polar Q h x)) hy
    have hxy' := mul_neg_of_pos_of_neg hb (mul_neg_of_pos_of_neg ha hxy)
    nlinarith only [hx', hy', hxy']
  have hhw : polar Q h w = 0 := by
    simp only [w, polar_sub_right, polar_smul_right, smul_eq_mul, mul_comm, sub_self]
  have hw₀ := eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh ((polar_comm Q w h).trans hhw) hw.le
  simp [hw₀] at hw

/-- The closed positive side of a vector of positive square is self-dual for the
polar pairing. -/
theorem nonneg_and_polar_nonneg_iff_forall (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h x : V} (hh : 0 < Q h) :
    (0 ≤ Q x ∧ 0 ≤ polar Q h x) ↔
      ∀ y, 0 ≤ Q y → 0 ≤ polar Q h y → 0 ≤ polar Q x y := by
  refine ⟨fun hx _ hy hhy ↦
    polar_nonneg_of_nonneg_of_polar_nonneg hQ hsig hh hx.1 hy hx.2 hhy, fun hdual ↦ ?_⟩
  have hhh : polar Q h h = 2 * Q h := by rw [polar_self, two_smul, two_mul]
  have hhx : 0 ≤ polar Q h x := by
    rw [polar_comm Q h x]
    exact hdual h hh.le (by rw [hhh]; positivity)
  refine ⟨?_, hhx⟩
  by_contra! hx
  have hxx : polar Q x x = 2 * Q x := by rw [polar_self, two_smul, two_mul]
  have htest (t : K) (ht : 0 ≤ t) (hq : 0 ≤ Q x + t ^ 2 * Q h + t * polar Q h x) :
      0 ≤ 2 * Q x + t * polar Q h x := by
    have hy : 0 ≤ Q (x + t • h) := by
      simpa only [QuadraticMap.map_add, QuadraticMap.map_smul, polar_smul_right,
        smul_eq_mul, polar_comm Q x h, pow_two] using hq
    have hyh : 0 ≤ polar Q h (x + t • h) := by
      rw [polar_add_right, polar_smul_right, smul_eq_mul, hhh]
      positivity
    simpa only [polar_add_right, polar_smul_right, smul_eq_mul, hxx, polar_comm Q x h]
      using hdual (x + t • h) hy hyh
  rcases hhx.eq_or_lt with hzero | hpos
  · -- Orthogonality makes the polar pairing independent of the shift.
    let t := 1 - Q x / Q h
    have ht : 1 ≤ t := by dsimp [t]; linarith [div_nonpos_of_nonpos_of_nonneg hx.le hh.le]
    have htQ : t * Q h = Q h - Q x := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hh.ne']
    have htQ' : Q h - Q x ≤ t ^ 2 * Q h := by
      rw [← htQ, pow_two, mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg (by linarith) hh.le) ht
    have := htest t (by linarith) (by rw [← hzero]; linarith)
    rw [← hzero, mul_zero, add_zero] at this
    linarith
  · -- The cross term cancels the negative square in the shifted vector.
    let t := -Q x / polar Q h x
    have ht : 0 ≤ t := div_nonneg (neg_nonneg.mpr hx.le) hpos.le
    have htQ : t * polar Q h x = -Q x := div_mul_cancel₀ _ hpos.ne'
    have hsq : 0 ≤ t ^ 2 * Q h := by positivity
    have := htest t ht (by rw [htQ]; linarith)
    rw [htQ] at this
    linarith

/-- A nonzero vector `d` of nonnegative square selects the same half of the positive
locus as a positive vector `h` with which it has nonnegative polar pairing. -/
theorem polar_pos_iff_of_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h d x : V} (hh : 0 < Q h) (hd : 0 ≤ Q d) (hd₀ : d ≠ 0)
    (hhd : 0 ≤ polar Q h d) (hx : 0 < Q x) :
    0 < polar Q d x ↔ 0 < polar Q h x := by
  have hdh₀ : polar Q d h ≠ 0 := fun he ↦
    hd₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh he hd)
  have hdh : 0 < polar Q d h := lt_of_le_of_ne (by rwa [polar_comm]) hdh₀.symm
  have hpos {y : V} (hy : 0 < Q y) (hhy : 0 < polar Q h y) : 0 < polar Q d y :=
    sign_eq_one_iff.mp
      ((sign_polar_eq_sign_polar hQ hsig hd hd₀ hh hy hhy).symm.trans (sign_pos hdh))
  refine ⟨fun hdx ↦ ?_, hpos hx⟩
  by_contra! hnot
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hhx₀ : polar Q h x ≠ 0 := fun he ↦ hx₀
    (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh (by rwa [polar_comm]) hx.le)
  have hneg : 0 < polar Q h (-x) := by
    rw [polar_neg_right]
    exact neg_pos.mpr (lt_of_le_of_ne hnot hhx₀)
  have := hpos (by simpa using hx : 0 < Q (-x)) hneg
  rw [polar_neg_right] at this
  exact (neg_pos.mp this).not_gt hdx

/-- The positive vectors that pair positively with a fixed positive vector form
a convex set. -/
theorem convex_setOf_pos_and_polar_pos (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : V} (hh : 0 < Q h) :
    Convex K {x | 0 < Q x ∧ 0 < polar Q h x} := by
  intro x hx y hy a b ha hb hab
  rw [Set.mem_ofPred_eq] at hx hy ⊢
  rcases eq_or_lt_of_le ha with ha₀ | ha'
  · subst a
    simp only [zero_add] at hab
    subst b
    simpa using hy
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxy := (polar_pos_iff_of_nonneg hQ hsig hh hx.1.le hx₀ hx.2.le hy.1).mpr hy.2
  constructor
  · simp only [QuadraticMap.map_add, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
      smul_eq_mul]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (mul_pos (mul_pos ha' ha') hx.1)
        (mul_nonneg (mul_nonneg hb hb) hy.1.le))
      (mul_nonneg hb (mul_nonneg ha hxy.le))
  · simp only [polar_add_right, polar_smul_right, smul_eq_mul]
    exact add_pos_of_pos_of_nonneg (mul_pos ha' hx.2) (mul_nonneg hb hy.2.le)

end QuadraticForm
