/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.CurveCone
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import Mathlib.RingTheory.Flat.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# Effective representatives on exceptional rays

An effective integral divisor of square `-1` whose class spans an extremal
ray of the closed curve cone is a prime divisor with coefficient one.
Extremality puts every prime in its support on the same ray. Two distinct
primes on that ray would have negative intersection, and the integral
intersection pairing forces the remaining coefficient to be one.

This is the irreducibility calculation used to transport exceptional curves in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 1.8](https://arxiv.org/pdf/1211.6367v5#page=14).
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open scoped TensorProduct

namespace TauCeti.AlgebraicGeometry.Chow

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "V(" S ")" => (ℝ ⊗[ℤ] Additive (LineBundleClass S))
local notation "B" => realIntersectionBilinForm k X
local notation "ι" => (fun a : Additive (LineBundleClass X) ↦ (1 : ℝ) ⊗ₜ[ℤ] a)
local notation "C" => closedCurveCone k (X := X)

local notation "cl" => weilToLineBundleClassHom X

section Factorial

variable [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

private theorem one_tmul_weilToLineBundleClassHom_eq_sum (D : SchemeWeilDivisor X) :
    ι (cl D) = ∑ p ∈ D.support, (D p : ℝ) • realPrimeDivisorClass k p := by
  classical
  conv_lhs => rw [WeilDivisor.eq_sum_coeff_smul_ofPoint D]
  simp only [map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← WeilDivisor.single_eq_zsmul_ofPoint, weilToLineBundleClassHom_single,
    realPrimeDivisorClass_def, LineBundleClass.primeDivisorClass_def,
    TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rfl

variable [Infinite k] [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)]
  [ContinuousSMul ℝ V(X)]

private theorem exists_pos_smul_eq_realPrimeDivisorClass_of_mem_support
    (D : SchemeWeilDivisor X) (hD : 0 ≤ D)
    (hface : (PointedCone.hull ℝ {ι (cl D)}).IsFaceOf (C).toPointedCone)
    (p : CodimensionOnePoint X) (hp : p ∈ D.support) :
    ∃ r : ℝ, 0 < r ∧ realPrimeDivisorClass k p = r • ι (cl D) := by
  classical
  let E := PointedCone.hull ℝ {ι (cl D)}
  have hsum : (∑ q : D.support, (D q.val : ℝ) • realPrimeDivisorClass k q.val) ∈ E := by
    rw [Finset.univ_eq_attach, Finset.sum_attach D.support
      (fun q ↦ (D q : ℝ) • realPrimeDivisorClass k q),
      ← one_tmul_weilToLineBundleClassHom_eq_sum k]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hmem := hface.mem_of_sum_smul_mem
    (fun q : D.support ↦ realPrimeDivisorClass_mem_closedCurveCone k q.val)
    (fun q : D.support ↦ Int.cast_nonneg ((WeilDivisor.nonneg_iff D).mp hD q.val)) hsum
    ⟨p, hp⟩ (Int.cast_pos.mpr
      (lt_of_le_of_ne ((WeilDivisor.nonneg_iff D).mp hD p) (Finsupp.mem_support_iff.mp hp).symm))
  obtain ⟨r, hr, hpr⟩ := PointedCone.mem_hull_singleton.mp hmem
  obtain ⟨a, ha⟩ := X.exists_isAmple_of_isProjectiveOver k
  have hpos := realIntersectionBilinForm_realPrimeDivisorClass_pos k ha p
  refine ⟨r, lt_of_le_of_ne hr (Ne.symm fun hr₀ ↦ ?_), hpr.symm⟩
  rw [hr₀, zero_smul] at hpr
  exact (ne_of_gt hpos) (by rw [← hpr, map_zero])

private theorem support_subsingleton_of_isEffective_of_extremalRay
    (D : SchemeWeilDivisor X) (hD : 0 ≤ D)
    (hface : (PointedCone.hull ℝ {ι (cl D)}).IsFaceOf (C).toPointedCone)
    (hneg : B (ι (cl D)) (ι (cl D)) < 0) :
    (D.support : Set (CodimensionOnePoint X)).Subsingleton := by
  intro p hp q hq
  by_contra hne
  obtain ⟨r, hr, heq⟩ := exists_pos_smul_eq_realPrimeDivisorClass_of_mem_support k D hD hface p hp
  obtain ⟨s, hs, heq'⟩ := exists_pos_smul_eq_realPrimeDivisorClass_of_mem_support k D hD hface q hq
  have hpos := realIntersectionBilinForm_realPrimeDivisorClass_nonneg k hne
  simp only [heq, heq', map_smul, LinearMap.smul_apply, smul_eq_mul] at hpos
  exact (not_lt_of_ge hpos) (mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg hr hneg))

end Factorial

variable [Infinite k] [TopologicalSpace V(X)] [IsTopologicalAddGroup V(X)]
  [ContinuousSMul ℝ V(X)]

/-- An effective integral divisor of self-intersection `-1` whose real class generates
an extremal ray is a prime divisor with multiplicity one. -/
theorem eq_single_of_isEffective_of_extremalRay
    (D : SchemeWeilDivisor X) (hD : 0 ≤ D) {p : CodimensionOnePoint X} (hp : p ∈ D.support) :
    letI : IsNoetherian X := isNoetherian_of_finiteType f
    letI := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (PointedCone.hull ℝ {ι (cl D)}).IsFaceOf (C).toPointedCone →
    classIntersectionNumber k X (cl D).toMul (cl D).toMul = -1 →
    D = Finsupp.single p 1 := by
  intro hface hsq
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  classical
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hneg : B (ι (cl D)) (ι (cl D)) < 0 := by simp [hsq]
  have hsub := support_subsingleton_of_isEffective_of_extremalRay k D hD hface hneg
  have hsingle : D = Finsupp.single p (D p) :=
    Finsupp.eq_single_iff.mpr ⟨fun q hq ↦ Finset.mem_singleton.mpr (hsub hq hp), rfl⟩
  have hclass : cl D = D p • Additive.ofMul (LineBundleClass.primeDivisorClass p) := by
    conv_lhs => rw [hsingle]
    rw [weilToLineBundleClassHom_single, LineBundleClass.primeDivisorClass_def]
  let I := classIntersectionBilinForm k hX
  have hI : I (cl D) (cl D) = -1 := by
    simpa only [I, classIntersectionBilinForm_apply] using hsq
  have hdvd : D p ∣ (-1 : ℤ) := by
    refine ⟨I (cl D) (Additive.ofMul (LineBundleClass.primeDivisorClass p)), ?_⟩
    calc
      -1 = I (cl D) (cl D) := hI.symm
      _ = I (cl D) (D p • Additive.ofMul (LineBundleClass.primeDivisorClass p)) :=
        congrArg (I (cl D)) hclass
      _ = _ := by simp only [map_zsmul, smul_eq_mul]
  have hpos : 0 < D p := lt_of_le_of_ne ((WeilDivisor.nonneg_iff D).mp hD p)
    (Finsupp.mem_support_iff.mp hp).symm
  have hone : D p = 1 := by
    have hu := (Int.isUnit_iff).mp (isUnit_iff_dvd_one.mpr (dvd_neg.mp hdvd))
    omega
  exact hsingle.trans (congrArg (Finsupp.single p) hone)

/-- An effective class of square `-1` on an extremal ray is represented by a unique prime
divisor. Effectivity is witnessed by a nonnegative Weil divisor in the class. -/
theorem existsUnique_primeDivisorClass_of_effective_extremalRay {a : LineBundleClass X}
    (hface : (PointedCone.hull ℝ {ι (Additive.ofMul a)}).IsFaceOf (C).toPointedCone)
    (hsq : classIntersectionNumber k X a a = -1) :
    letI : IsNoetherian X := isNoetherian_of_finiteType f
    letI := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ (cl D).toMul = a) →
    ∃! p : CodimensionOnePoint X, LineBundleClass.primeDivisorClass p = a := by
  intro ha
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨D, hD, hclass⟩ := ha
  have he : cl D = Additive.ofMul a := congrArg Additive.ofMul hclass
  have hface' : (PointedCone.hull ℝ {ι (cl D)}).IsFaceOf (C).toPointedCone := by rwa [he]
  have hsq' : classIntersectionNumber k X (cl D).toMul (cl D).toMul = -1 := by rwa [hclass]
  have hD₀ : D ≠ 0 := by
    rintro rfl
    simp [classIntersectionNumber_one_right] at hsq'
  obtain ⟨p, hp₀⟩ := Finsupp.support_nonempty_iff.mpr hD₀
  have hDp := eq_single_of_isEffective_of_extremalRay k D hD hp₀ hface' hsq'
  rw [hDp] at hclass
  have hp : LineBundleClass.primeDivisorClass p = a := by
    simpa only [weilToLineBundleClassHom_single, one_smul, toMul_ofMul,
      LineBundleClass.primeDivisorClass_def] using hclass
  refine ⟨p, hp, fun q hq ↦ ?_⟩
  by_contra hne
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hh := classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX hne
  rw [hq, hp, hsq] at hh
  omega

open Scheme.IdealSheafData in
omit [Infinite k] in
/-- A class of square and canonical degree `-1` spanning an extremal ray of the
closed curve cone is effective. A prime on the ray is a positive real multiple of
the given class. Its integral canonical degree and arithmetic genus force the
multiple to be one. -/
theorem exists_effectiveWeilDivisor_of_exceptional_extremalRay [IsAlgClosed k]
    [Scheme.IsRationalOver f] [FiniteDimensional ℝ V(X)] [T2Space V(X)]
    {a : LineBundleClass X}
    (hface : (PointedCone.hull ℝ {ι (Additive.ofMul a)}).IsFaceOf (C).toPointedCone)
    (hsq : classIntersectionNumber k X a a = -1)
    (hcan : classIntersectionNumber k X a
      (LineBundleClass.mk (QPainleve.canonicalBundle k X 2)) = -1) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
      (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    ∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ (cl D).toMul = a := by
  intro _ _
  let K := LineBundleClass.mk (QPainleve.canonicalBundle k X 2)
  let P := LineBundleClass.primeDivisorClass (X := X)
  let I := classIntersectionNumber k X
  obtain ⟨p, r, hr, he⟩ := exists_realPrimeDivisorClass_eq_pos_smul_of_isFaceOf_hull_singleton
    k hface (by simp [hsq])
  have hdeg : (I (P p) K : ℝ) = -r := by
    dsimp only [I, P]
    rw [classIntersectionNumber_comm,
      ← realIntersectionBilinForm_one_tmul_realPrimeDivisorClass k K p,
      (isSymm_realIntersectionBilinForm k X).eq, he, map_smul, LinearMap.smul_apply]
    simp [K, hcan]
  have hself : (I (P p) (P p) : ℝ) = -(r ^ 2) := by
    rw [← realIntersectionBilinForm_one_tmul_realPrimeDivisorClass k (P p) p,
      ← realPrimeDivisorClass_def k p, he]
    simp [hsq, pow_two, map_smul, LinearMap.smul_apply]
  have hdeg₀ : I (P p) K < 0 := by exact_mod_cast hdeg.trans_lt (neg_neg_of_pos hr)
  have hdeg₁ : I (P p) K ≤ -1 := by omega
  have hdegℝ : (I (P p) K : ℝ) ≤ -1 := by exact_mod_cast hdeg₁
  have hadj := two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  dsimp only at hadj
  have hboundℤ : -2 ≤ I (P p) (P p) + I (P p) K := by
    dsimp only [I, P, K]
    omega
  have hbound : (-2 : ℝ) ≤ (I (P p) (P p) : ℝ) + (I (P p) K : ℝ) := by
    exact_mod_cast hboundℤ
  have hr₁ : r = 1 := by nlinarith [sq_nonneg (r - 1)]
  have : Module.Free ℤ (Additive (LineBundleClass X)) := X.free_picard_of_isRationalOver k
  have he' : ι (Additive.ofMul (P p)) = ι (Additive.ofMul a) := by
    simpa only [realPrimeDivisorClass_def, hr₁, one_smul] using he
  have hc := congrArg Additive.toMul
    (Module.Flat.tensorProduct_mk_injective ℤ (Additive (LineBundleClass X)) ℝ he')
  refine ⟨Finsupp.single p 1, by simp, ?_⟩
  simpa only [P, toMul_ofMul, weilToLineBundleClassHom_single, one_smul,
    ← LineBundleClass.primeDivisorClass_def] using hc

open Scheme.IdealSheafData in
omit [Infinite k] in
/-- An effective class of square `-1` and canonical degree `-1` on an extremal ray
of a smooth projective rational surface is represented by a unique prime divisor,
and its reduced closure is an exceptional curve of the first kind. -/
theorem existsUnique_exceptionalPrimeDivisor_of_effective_extremalRay [IsAlgClosed k]
    [Scheme.IsRationalOver f] {a : LineBundleClass X}
    (hface : (PointedCone.hull ℝ {ι (Additive.ofMul a)}).IsFaceOf (C).toPointedCone)
    (hsq : classIntersectionNumber k X a a = -1)
    (hcan : classIntersectionNumber k X a
      (LineBundleClass.mk (QPainleve.canonicalBundle k X 2)) = -1) :
    letI : IsNoetherian X := isNoetherian_of_finiteType f
    letI := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ (cl D).toMul = a) →
    ∃! p : CodimensionOnePoint X, LineBundleClass.primeDivisorClass p = a ∧
      (vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩).IsExceptionalCurveOfFirstKind := by
  intro ha
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨p, hp, huniq⟩ := existsUnique_primeDivisorClass_of_effective_extremalRay k hface hsq ha
  refine ⟨p, ⟨hp, ?_⟩, fun q hq ↦ huniq q hq.1⟩
  let J := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have hJ : J.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hdim := QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p
  have : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  have : J.subscheme.IsCurveOver k :=
    Scheme.isCurveOver_iff.mpr ⟨inferInstance, inferInstance, hdim⟩
  have hclass : (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ = a := by
    simpa only [LineBundleClass.primeDivisorClass_def] using hp
  have hadj : 2 * (J.subscheme.genus k : ℤ) - 2 =
      classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.primeDivisorClass p) +
      classIntersectionNumber k X (LineBundleClass.primeDivisorClass p)
        (LineBundleClass.mk (QPainleve.canonicalBundle k X 2)) :=
    two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  rw [hp, hsq, hcan] at hadj
  have hex := hJ.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    (k := k) hX.le
  dsimp only at hex
  rw [hclass, hsq] at hex
  exact hex.mpr ⟨by omega, rfl⟩

end TauCeti.AlgebraicGeometry.Chow
