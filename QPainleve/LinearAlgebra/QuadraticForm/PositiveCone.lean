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
The comparison uses Tau Ceti's `QuadraticForm.sign_polar_eq_sign_polar`.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

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
