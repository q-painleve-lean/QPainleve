/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.LinearAlgebra.QuadraticForm.LightCone

import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Topology.ConnectedComponents

/-!
# Components of the positive cone

For a nondegenerate real quadratic form of positive index one, pairing with a positive vector
identifies its component of the positive cone. The closure is cut out by the corresponding weak
inequalities, and any two of its vectors have nonnegative pairing. A nonzero isotropic vector in
that closure identifies the same open component by strict positivity of the pairing.

The algebraic input is Tau Ceti's `QuadraticForm.eq_zero_of_polar_eq_zero_of_nonneg`.
The component comparison uses `TauCeti.connectedComponentIn_eq_of_lt`.
-/

public section

open Set
open QuadraticMap

namespace QuadraticForm

section OrderedField

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M] {Q : QuadraticForm K M}

/-- Two vectors of nonnegative square on the same closed side of a positive vector have
nonnegative polar pairing. -/
theorem polar_nonneg_of_nonneg_of_polar_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h x y : M} (hh : 0 < Q h) (hx : 0 ≤ Q x) (hy : 0 ≤ Q y)
    (hxh : 0 ≤ polar Q x h) (hyh : 0 ≤ polar Q y h) : 0 ≤ polar Q x y := by
  by_contra! hxy
  have hx₀ : x ≠ 0 := by rintro rfl; simp at hxy
  have hy₀ : y ≠ 0 := by rintro rfl; simp at hxy
  have ha : 0 < polar Q y h := lt_of_le_of_ne hyh fun he ↦
    hy₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh he.symm hy)
  have hb : 0 < polar Q x h := lt_of_le_of_ne hxh fun he ↦
    hx₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh he.symm hx)
  -- A negative pairing would make this vector positive even though it is orthogonal to h.
  let w := polar Q y h • x - polar Q x h • y
  have hw : 0 < Q w := by
    simp only [w, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.map_smul, polar_neg_right, polar_smul_left, polar_smul_right, smul_eq_mul]
    have hx' := mul_nonneg (mul_self_nonneg (polar Q y h)) hx
    have hy' := mul_nonneg (mul_self_nonneg (polar Q x h)) hy
    have hxy' := mul_neg_of_pos_of_neg hb (mul_neg_of_pos_of_neg ha hxy)
    nlinarith only [hx', hy', hxy']
  have hwh : polar Q w h = 0 := by
    simp only [w, polar_sub_left, polar_smul_left, smul_eq_mul, mul_comm, sub_self]
  have := eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh hwh hw.le
  simp [this] at hw

/-- For two vectors of nonnegative square on the same closed side, the polar pairing is
positive if one has positive square and the other is nonzero. -/
theorem polar_pos_of_pos_of_polar_nonneg (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h x y : M} (hh : 0 < Q h) (hx : 0 < Q x) (hy : 0 ≤ Q y) (hy₀ : y ≠ 0)
    (hxh : 0 ≤ polar Q x h) (hyh : 0 ≤ polar Q y h) : 0 < polar Q x y :=
  lt_of_le_of_ne (polar_nonneg_of_nonneg_of_polar_nonneg hQ hsig hh hx.le hy hxh hyh)
    (fun he ↦ hy₀ (eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hx
      ((polar_comm Q y x).trans he.symm) hy))

/-- The positive vectors pairing positively with a given positive vector form a convex set. -/
theorem convex_setOf_pos_and_polar_pos (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : M} (hh : 0 < Q h) : Convex K {x | 0 < Q x ∧ 0 < polar Q x h} := by
  rintro x ⟨hx, hxh⟩ y ⟨hy, hyh⟩ a b ha hb hab
  have hs : 0 < a ∨ 0 < b := by
    by_contra! h
    exact zero_lt_one.not_ge (hab ▸ add_nonpos h.1 h.2)
  have hxy := polar_nonneg_of_nonneg_of_polar_nonneg hQ hsig hh hx.le hy.le hxh.le hyh.le
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      polar_smul_left, polar_smul_right]
    have hcross : 0 ≤ a * (b * polar Q x y) := mul_nonneg ha (mul_nonneg hb hxy)
    simp only [smul_eq_mul]
    rcases hs with ha' | hb'
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (mul_pos (mul_pos ha' ha') hx)
          (mul_nonneg (mul_nonneg hb hb) hy.le)) hcross
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg ha ha) hx.le)
          (mul_pos (mul_pos hb' hb') hy)) hcross
  · rw [polar_add_left, polar_smul_left, polar_smul_left]
    simp only [smul_eq_mul]
    exact hs.elim
      (fun ha' ↦ add_pos_of_pos_of_nonneg (mul_pos ha' hxh) (mul_nonneg hb hyh.le))
      (fun hb' ↦ add_pos_of_nonneg_of_pos (mul_nonneg ha hxh.le) (mul_pos hb' hyh))

end OrderedField

section Real

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {Q : QuadraticForm ℝ M}

/-- The component of the positive cone containing `h` consists of the positive vectors with
positive polar pairing with `h`. -/
theorem connectedComponentIn_pos_eq (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : M} (hh : 0 < Q h) :
    connectedComponentIn {x | 0 < Q x} h = {x | 0 < Q x ∧ 0 < polar Q x h} := by
  have hh' : 0 < polar Q h h := by simpa [polar_self, two_nsmul] using add_pos hh hh
  have hcont : Continuous (fun x ↦ polar Q x h) :=
    (Q.polarBilin.flip h).continuous_of_finiteDimensional
  refine TauCeti.connectedComponentIn_eq_of_lt (φ := fun x ↦ polar Q x h)
    (Convex.isPreconnected (convex_setOf_pos_and_polar_pos hQ hsig hh))
    (fun _ hx ↦ hx.1) ⟨hh, hh'⟩ hh' hcont.continuousOn ?_ (fun _ hx hp ↦ ⟨hx, hp⟩)
  intro x hx he
  have hz := eq_zero_of_polar_eq_zero_of_nonneg hQ hsig hh he (le_of_lt hx)
  simp [hz] at hx

/-- A positive-cone component closes up to the vectors satisfying both weak inequalities. -/
theorem closure_connectedComponentIn_pos_eq (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1)
    {h : M} (hh : 0 < Q h) :
    closure (connectedComponentIn {x | 0 < Q x} h) =
      {x | 0 ≤ Q x ∧ 0 ≤ polar Q x h} := by
  rw [connectedComponentIn_pos_eq hQ hsig hh]
  refine Subset.antisymm ?_ ?_
  · have hcontQ : Continuous Q := by
      have : IsModuleTopology ℝ M := isModuleTopologyOfFiniteDimensional
      have hpair : Continuous (fun p : M × M ↦ polar Q p.1 p.2) :=
        IsModuleTopology.continuous_bilinear_of_finite_left (R := ℝ) (A := M) (B := M)
          (C := ℝ) Q.polarBilin
      have hdiag : Continuous (fun z ↦ polar Q z z) :=
        hpair.comp (continuous_id.prodMk continuous_id)
      simpa only [polar_self, two_nsmul, add_self_div_two] using hdiag.div_const 2
    have hcontP : Continuous (fun x ↦ polar Q x h) :=
      (Q.polarBilin.flip h).continuous_of_finiteDimensional
    exact closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)
      ((isClosed_le continuous_const hcontQ).inter (isClosed_le continuous_const hcontP))
  · rintro x ⟨hx, hxh⟩
    have hh' : 0 < polar Q h h := by simpa [polar_self, two_nsmul] using add_pos hh hh
    have hzero : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
    have hmem := map_mem_closure (f := fun t : ℝ ↦ x + t • h) (by fun_prop) hzero
      (t := {x | 0 < Q x ∧ 0 < polar Q x h}) fun t (ht : 0 < t) ↦ by
        simp only [Set.mem_ofPred_eq, QuadraticMap.map_add Q, QuadraticMap.map_smul,
          polar_smul_right, polar_add_left, polar_smul_left, smul_eq_mul]
        exact ⟨add_pos_of_pos_of_nonneg
          (add_pos_of_nonneg_of_pos hx (mul_pos (mul_pos ht ht) hh)) (mul_nonneg ht.le hxh),
          add_pos_of_nonneg_of_pos hxh (mul_pos ht hh')⟩
    simpa only [zero_smul, add_zero] using hmem

/-- The pairing is nonnegative on the closure of a single positive-cone component. -/
theorem polar_nonneg_of_mem_closure_connectedComponentIn_pos
    (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1) {h x y : M} (hh : 0 < Q h)
    (hx : x ∈ closure (connectedComponentIn {x | 0 < Q x} h))
    (hy : y ∈ closure (connectedComponentIn {x | 0 < Q x} h)) :
    0 ≤ polar Q x y := by
  rw [closure_connectedComponentIn_pos_eq hQ hsig hh] at hx hy
  exact polar_nonneg_of_nonneg_of_polar_nonneg hQ hsig hh hx.1 hy.1 hx.2 hy.2

/-- A nonzero vector in the closure, in particular a nonzero isotropic vector in it, identifies
the open component by its polar pairing with positive vectors. -/
theorem connectedComponentIn_pos_eq_of_mem_closure
    (hQ : Q.Nondegenerate) (hsig : sigPos Q ≤ 1) {h d : M} (hh : 0 < Q h)
    (hd₀ : d ≠ 0) (hd : d ∈ closure (connectedComponentIn {x | 0 < Q x} h)) :
    connectedComponentIn {x | 0 < Q x} h = {x | 0 < Q x ∧ 0 < polar Q x d} := by
  rw [closure_connectedComponentIn_pos_eq hQ hsig hh] at hd
  rw [connectedComponentIn_pos_eq hQ hsig hh]
  ext x
  refine ⟨fun hx ↦ ⟨hx.1, polar_pos_of_pos_of_polar_nonneg hQ hsig hh
    hx.1 hd.1 hd₀ hx.2.le hd.2⟩, fun hx ↦ ⟨hx.1, ?_⟩⟩
  by_contra! hxh
  have hnx : 0 < Q (-x) := by simpa only [QuadraticMap.map_neg] using hx.1
  have hnxh : 0 ≤ polar Q (-x) h := by simpa only [polar_neg_left, neg_nonneg] using hxh
  have hnxd := polar_pos_of_pos_of_polar_nonneg hQ hsig hh hnx hd.1 hd₀ hnxh hd.2
  rw [polar_neg_left, neg_pos] at hnxd
  exact hnxd.not_gt hx.2

end Real

end QuadraticForm
