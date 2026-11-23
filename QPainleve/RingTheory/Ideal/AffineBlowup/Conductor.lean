/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.Conductor
public import TauCeti.RingTheory.Ideal.AffineBlowup

/-!
# Conductors of affine blowup algebras

If an ideal satisfies `I² = aI`, then multiplying an element of the affine blowup
chart `A[I/a]` by an element of `I` gives the image of an element of `I`.
In particular the chart conductor contains the center ideal.
-/

public section

open IsLocalRing
open scoped TensorProduct

namespace Ideal

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
  {I : Ideal A} {a : A} [IsLocalization.Away a S]

/-- If `I² = aI`, then the conductor of the chart `A[I/a]` contains `I`. -/
theorem le_conductor_affineBlowup_of_sq_le (ha : a ∈ I)
    (hI : I ^ 2 ≤ Ideal.span {a} * I) :
    I ≤ TauCeti.Algebra.conductor A (I.affineBlowup a S) := by
  have hpow (n : ℕ) : I * I ^ n ≤ Ideal.span {a ^ n} * I := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        I * I ^ (n + 1) = I ^ 2 * I ^ n := by
          rw [pow_succ', pow_two, mul_assoc]
        _ ≤ (Ideal.span {a} * I) * I ^ n := Ideal.mul_mono_left hI
        _ ≤ Ideal.span {a} * (Ideal.span {a ^ n} * I) := by
          rw [mul_assoc]
          exact Ideal.mul_mono_right ih
        _ = Ideal.span {a ^ (n + 1)} * I := by
          rw [← mul_assoc, span_singleton_mul_span_singleton, pow_succ']
  intro x hx
  rw [TauCeti.Algebra.mem_conductor_iff]
  intro b
  obtain ⟨n, y, hy, hby⟩ := (mem_affineBlowup_iff ha).mp b.property
  obtain ⟨z, _, hz⟩ := mem_span_singleton_mul.mp (hpow n (mul_mem_mul hx hy))
  refine ⟨z, Subtype.ext ?_⟩
  -- Work in the localization, where the chart denominator can be cancelled.
  change algebraMap A S z = algebraMap A S x * (b : S)
  apply ((IsLocalization.Away.algebraMap_isUnit (S := S) a).pow n).mul_left_cancel
  rw [← map_pow, ← map_mul, hz, map_mul, map_pow, mul_left_comm, hby]

/-- The conductor of a two-generated maximal ideal's affine blowup chart is that
maximal ideal if the second generator squares into `a𝔪` and the closed fiber has
dimension greater than one. -/
theorem conductor_affineBlowup_eq_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {a b : R} (hI : Ideal.span {a, b} = maximalIdeal R)
    (hb : b ^ 2 ∈ Ideal.span {a} * maximalIdeal R)
    (hr : 1 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] (maximalIdeal R).affineBlowup a (Localization.Away a))) :
    TauCeti.Algebra.conductor R ((maximalIdeal R).affineBlowup a (Localization.Away a)) =
      maximalIdeal R := by
  let B := (maximalIdeal R).affineBlowup a (Localization.Away a)
  have ha : a ∈ maximalIdeal R := hI ▸ Ideal.subset_span (Set.mem_insert a _)
  have hbI : b ∈ maximalIdeal R :=
    hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ha' : a ∈ (Ideal.span {a} : Ideal R) := Ideal.subset_span (Set.mem_singleton _)
  have hab : a * b ∈ Ideal.span {a} * maximalIdeal R := Ideal.mul_mem_mul ha' hbI
  have hba : b * a ∈ Ideal.span {a} * maximalIdeal R := mul_comm a b ▸ hab
  have hbb : b * b ∈ Ideal.span {a} * maximalIdeal R := by
    rw [← pow_two]
    exact hb
  have hsq : maximalIdeal R ^ 2 ≤ Ideal.span {a} * maximalIdeal R := by
    conv_lhs => rw [pow_two, ← hI, Ideal.span_mul_span]
    rw [Ideal.span_le]
    rintro _ ⟨v, hv, w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Ideal.mul_mem_mul ha' ha
    · exact hab
    · exact hba
    · exact hbb
  refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) (le_conductor_affineBlowup_of_sq_le ha hsq)
  intro h
  have hs : Function.Surjective (algebraMap R B) := TauCeti.Algebra.conductor_eq_top_iff.mp h
  let K := IsLocalRing.ResidueField R
  have hf := LinearMap.finrank_le_finrank_of_surjective
    (f := (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[R] B).toLinearMap)
    (Algebra.TensorProduct.includeLeft_surjective K K hs)
  rw [Module.finrank_self] at hf
  exact (not_lt_of_ge hf) hr

end Ideal
