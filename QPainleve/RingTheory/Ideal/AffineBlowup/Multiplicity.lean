/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.Ideal.AffineBlowup.Basic
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.RingTheory.Regular.DSequence

/-!
# Contraction of ideal powers on affine blowup charts

The extension of a regularly generated center to a standard chart is principal.
Its powers contract back to the corresponding powers of the center.

The contraction uses Tau Ceti's Goto–Yamagishi intersection identity
`TauCeti.IsDSequence.inf_pow_smul_top_eq`.
-/

public section

open RingTheory.Sequence

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R} {a : R}
  {S : Type*} [CommRing S] [Algebra R S] [IsLocalization.Away a S]

/-- In the chart of the first term of a weakly regular generating sequence, extending and
contracting a power of the center gives the original power. -/
theorem algebraMap_mem_map_pow_affineBlowup_iff {rs : List R}
    (h : IsWeaklyRegular R (a :: rs)) (hI : ofList (a :: rs) = I) (n : ℕ) (f : R) :
    algebraMap R (I.affineBlowup a S) f ∈
        (I ^ n).map (algebraMap R (I.affineBlowup a S)) ↔ f ∈ I ^ n := by
  refine ⟨?_, mem_map_of_mem _⟩
  intro hf
  have ha : a ∈ I := by
    rw [← hI, ofList_cons]
    exact (le_sup_left : span {a} ≤ span {a} ⊔ ofList rs) (mem_span_singleton_self a)
  have haReg := ((isWeaklyRegular_cons_iff R a rs).mp h).1
  have haCancel : IsRegular a := (Commute.isRegular_iff (Commute.all a)).mpr haReg
  have hInj : Function.Injective (algebraMap R S) :=
    IsLocalization.injectiveₛ (M := Submonoid.powers a) S (by
      rintro _ ⟨k, rfl⟩
      exact haCancel.pow k)
  -- The intersection formula lets us cancel one factor of the chart parameter in the filtration.
  have hStep (k : ℕ) {x : R} (hx : a * x ∈ I ^ (k + 1)) : x ∈ I ^ k := by
    have heq : span {a} ⊓ I ^ (k + 1) = I ^ k * span {a} := by
      simpa [ofList_cons, hI, mul_comm (span {a} : Ideal R)] using
        h.isDSequence.inf_pow_smul_top_eq 1 (n := k + 1) (Nat.succ_ne_zero k)
    have hx' : a * x ∈ I ^ k * span {a} := heq ▸
      mem_inf.mpr ⟨mem_span_singleton.mpr (dvd_mul_right a x), hx⟩
    obtain ⟨y, hy, hxy⟩ := mem_mul_span_singleton.mp hx'
    exact (haReg (by simpa [mul_comm, smul_eq_mul] using hxy.symm) : x = y) ▸ hy
  have hCancel (k : ℕ) {x : R} (hx : a ^ k * x ∈ I ^ (n + k)) : x ∈ I ^ n := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      apply ih
      apply hStep (n + k)
      simpa [pow_succ', mul_assoc, Nat.add_assoc] using hx
  rw [Ideal.map_pow, map_algebraMap_affineBlowup ha, span_singleton_pow,
    mem_span_singleton] at hf
  obtain ⟨z, hz⟩ := hf
  obtain ⟨k, y, hy, hyz⟩ := (mem_affineBlowup_iff ha).mp z.property
  apply hCancel k
  have heq : a ^ k * f = a ^ n * y := hInj (by
    simp only [map_mul, map_pow]
    have hz' : algebraMap R S f = algebraMap R S a ^ n * (z : S) := by
      simpa only [map_mul, map_pow, AlgHom.commutes, Subalgebra.val_apply] using
        congrArg (I.affineBlowup a S).val hz
    rw [hz', mul_left_comm, hyz])
  rw [heq, pow_add]
  exact mul_mem_mul (pow_mem_pow ha n) hy

end Ideal
