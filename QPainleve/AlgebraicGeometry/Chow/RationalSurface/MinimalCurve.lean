/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical

import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Pluricanonical
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RankOne
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RiemannRoch
import QPainleve.AlgebraicGeometry.Curves.GenusZero
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import Mathlib.Data.Nat.Order.Lemmas

/-!
# Rational curves on minimal rational surfaces

A smooth projective rational surface without exceptional curves contains a projective
line of nonnegative self-intersection. An effective class of negative canonical degree
with ineffective adjoint supplies a prime component of arithmetic genus zero.
The proof uses an anticanonical decomposition or the last effective canonical twist,
according to the canonical square.

The adjoint argument follows [Vakil, *Complex Algebraic Surfaces*, Class 16, §2][Vakil16]
and [Class 17, §1][Vakil17].

[Vakil16]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
[Vakil17]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow
open TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open LinearMap.BilinForm

universe u

variable (k : Type u) [Field k] [algClosed : IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => X ↘ S
local notation "Pic" => Additive (LineBundleClass X)
local notation "K" => Additive.ofMul (mk (canonicalBundle k X 2))
local notation "P(" p ")" => Additive.ofMul (primeDivisorClass p)
local notation "cl" => weilToLineBundleClassHom X
local notation "E" => X.effectiveClasses
local notation "B" => intersectionBilinForm k X
local notation "dim₂" => topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)

local notation "C(" p ")" => vanishingIdeal (X := X)
  (TopologicalSpace.Closeds.mk (closure {(p : X)}) isClosed_closure)

namespace AlgebraicGeometry.Scheme

section Integral

variable [IsIntegral X]

include rational in
private theorem mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos (a : Pic)
    (ha : 0 < eulerCharBelow k a.toMul 3) : a ∈ E ∨ K - a ∈ E := by
  obtain ⟨I, hI, hclass | hclass⟩ :=
    exists_effectiveCartier_or_canonical_mul_inv_of_eulerCharBelow_pos k a.toMul ha
  · exact Or.inl (mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_toMul]⟩)
  · exact Or.inr (mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_mul, ofMul_inv, ofMul_toMul,
          sub_eq_add_neg]⟩)

include rational in
private theorem two_nsmul_canonical_notMem_effectiveClasses : (2 : ℕ) • K ∉ E := by
  intro he
  obtain ⟨D, hD, hclass⟩ := mem_effectiveClasses.mp he
  let L := (canonicalBundle k X 2).tensorPow 2
  have hL : D.toLineBundleClass = LineBundleClass.mk L := by
    simpa only [L, mk_tensorPow, toMul_nsmul, toMul_ofMul] using congrArg Additive.toMul hclass
  obtain ⟨e⟩ := toLineBundleClass_eq_mk_iff.mp hL
  have := X.subsingleton_cohomology_zero_pluricanonical_of_isRationalOver k (by decide : 0 < 2)
  have : Subsingleton (Cohomology D.sheaf 0) :=
    (cohomologyBaseLinearEquivOfIso k e 0).injective.subsingleton
  have : Subsingleton (Γ(D.sheaf, ⊤)) :=
    (cohomologyZeroBaseLinearEquiv k X D.sheaf).surjective.subsingleton
  have heq : Scheme.Modules.Hom.app (D.unitToSheaf hD) ⊤ (1 : Γ(X, ⊤)) = 0 := Subsingleton.elim _ _
  have hs : Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) ⊤ (1 : Γ(X, ⊤)) = 0 := calc
    _ = Scheme.Modules.Hom.app (D.unitToSheaf hD ≫ D.sheafι) ⊤ (1 : Γ(X, ⊤)) :=
      congrArg (fun g ↦ Scheme.Modules.Hom.app g ⊤ (1 : Γ(X, ⊤))) (D.unitToSheaf_ι hD).symm
    _ = Scheme.Modules.Hom.app D.sheafι ⊤
        (Scheme.Modules.Hom.app (D.unitToSheaf hD) ⊤ (1 : Γ(X, ⊤))) := rfl
    _ = 0 := by rw [heq, map_zero]
  exact ((Scheme.toRationalFunctions_app_injective (X := X) ⊤).ne
    (one_ne_zero : (1 : Γ(X, ⊤)) ≠ 0)) (hs.trans (map_zero _).symm)

include rational in
private theorem anticanonical_mem_effectiveClasses (hK : 0 ≤ B K K) : -K ∈ E := by
  have hRR : 2 * (eulerCharBelow k (-K : Pic).toMul 3 - 1) = B (-K) (-K) - B (-K) K := by
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      eulerCharBelow_eq_riemannRoch_of_isRationalOver k (-K : Pic).toMul
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at hRR
  rcases mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos k (-K) (by omega) with h | h
  · exact h
  · exact (two_nsmul_canonical_notMem_effectiveClasses k) (by simpa [two_nsmul] using h) |>.elim

omit rational in
private theorem intersection_nonneg_of_mem_effectiveClasses {h a : Pic}
    (hh : h.toMul.IsNef k f) (ha : a ∈ E) : 0 ≤ B h a := by
  obtain ⟨D, hD, rfl⟩ := mem_effectiveClasses.mp ha
  rw [intersectionBilinForm_apply, toMul_ofMul, ← inv_inv D.toLineBundleClass,
    ← hD.mk_idealSheaf_eq_inv]
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  exact classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k dim₂ hh
    hD.isEffectiveCartier_idealSheaf

variable [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

omit rational in
private theorem intersection_pos_of_mem_effectiveClasses {h a : Pic}
    (hh : h.toMul.IsAmple) (ha : a ∈ E) (hne : a ≠ 0) : 0 < B h a := by
  obtain ⟨D, hD, rfl⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp ha
  simpa only [intersectionBilinForm_apply] using
    classIntersectionNumber_weilToLineBundleClassHom_pos_of_isAmple k dim₂ hh hD
      (fun h ↦ hne (by rw [h, map_zero]))

omit rational [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
private theorem exists_last_effective_adjoint {h a : Pic}
    (hnef : h.toMul.IsNef k f) (hK : B h K < 0) (ha : a ∈ E) :
    ∃ n : ℕ, a + n • K ∈ E ∧ a + (n + 1) • K ∉ E := by
  have hlarge : ∃ n : ℕ, a + n • K ∉ E := by
    refine ⟨(B h a).toNat + 1, fun he ↦ ?_⟩
    have hpos := intersection_nonneg_of_mem_effectiveClasses k hnef he
    rw [map_add, map_nsmul] at hpos
    have hm := mul_le_mul_of_nonneg_left (show B h K ≤ -1 by omega)
      (Int.natCast_nonneg ((B h a).toNat + 1))
    simp only [nsmul_eq_mul, mul_neg, mul_one] at hpos hm
    omega
  simpa only [not_not] using
    Nat.exists_not_and_succ_of_not_zero_of_exists (by simpa using ha) hlarge

omit rational in
private theorem exists_component_of_intersection_nonpos {a b : Pic}
    (ha : a ∈ E) (hne : a ≠ 0) (hab : B b a ≤ 0) :
    ∃ p : CodimensionOnePoint X, B b P(p) ≤ 0 ∧ (B b a < 0 → B b P(p) < 0) ∧
      a - P(p) ∈ E := by
  classical
  obtain ⟨D, hD, rfl⟩ := mem_effectiveClasses_iff_exists_weilDivisor.mp ha
  have hD₀ : D ≠ 0 := fun h ↦ hne (by rw [h, map_zero])
  have hpos {p : CodimensionOnePoint X} (hp : p ∈ D.support) : 0 < D p :=
    lt_of_le_of_ne (hD p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  have hsum : B b (cl D) = ∑ p ∈ D.support, D p * B b P(p) := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_weilToLineBundleClassHom k dim₂,
      Finsupp.sum, toMul_ofMul]
  have hex : ∃ p ∈ D.support, B b P(p) ≤ 0 ∧ (B b (cl D) < 0 → B b P(p) < 0) := by
    by_cases hlt : B b (cl D) < 0
    · by_contra! h
      refine hlt.not_ge (hsum ▸ Finset.sum_nonneg fun p hp ↦ mul_nonneg (hD p) ?_)
      by_contra! hn
      exact (h p hp hn.le).2.not_gt hn
    · by_contra! h
      refine hab.not_gt (hsum ▸ Finset.sum_pos (fun p hp ↦ mul_pos (hpos hp) ?_)
        (Finsupp.support_nonempty_iff.mpr hD₀))
      exact lt_of_not_ge fun he ↦ False.elim (hlt (h p hp he).1)
  obtain ⟨p, hp, hbp, hlt⟩ := hex
  have hle : Finsupp.single p 1 ≤ D := by
    intro q
    by_cases hqp : p = q
    · subst q
      simpa only [Finsupp.single_eq_same] using (show 1 ≤ D p by have := hpos hp; omega)
    · simpa only [Finsupp.single_apply, ite_eq_right hqp, Finsupp.zero_apply] using hD q
  exact ⟨p, hbp, hlt, mem_effectiveClasses_iff_exists_weilDivisor.mpr
    ⟨D - Finsupp.single p 1, sub_nonneg.mpr hle, by
      simp only [map_sub, weilToLineBundleClassHom_single, one_smul, ← primeDivisorClass_def]⟩⟩

omit rational in
private theorem isNef_primeDivisorClass_of_self_nonneg
    (p : CodimensionOnePoint X) (hp : 0 ≤ B P(p) P(p)) :
    (primeDivisorClass p).IsNef k f := by
  classical
  have h : cl (Finsupp.single p 1) = P(p) := by
    rw [weilToLineBundleClassHom_single, one_smul, primeDivisorClass_def]
  have hn := (isNef_weilToLineBundleClassHom_iff k dim₂
    (D := Finsupp.single p 1) (by simp)).mpr
  rw [h, toMul_ofMul] at hn
  apply hn
  intro q hq
  have he : q = p := by simpa only [Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton] using hq
  subst q
  simpa only [intersectionBilinForm_apply, toMul_ofMul] using hp

omit rational [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
private theorem exists_positive_class_of_canonical_square_neg {h : Pic}
    (hh : 0 < B h h) (hd₀ : 0 ≤ B h K) (hn : B K K < 0) :
    ∃ y : Pic, 0 < B y y ∧ 0 < B h y ∧ B y K < 0 := by
  have hsym (a b : Pic) : B a b = B b a := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  let q : ℤ := -(B K K)
  let d : ℤ := B h K
  have hq : 0 < q := neg_pos.mpr hn
  -- First move onto the orthogonal of the canonical class, then add it once.
  let x : Pic := q • h + d • K
  have hxK : B x K = 0 := by
    simp only [x, add_left, smul_left, q, d]
    ring
  have hhx : 0 < B h x := by
    simp only [x, add_right, smul_right]
    exact add_pos_of_pos_of_nonneg (mul_pos hq hh) (mul_self_nonneg d)
  have hxx : B x x = q * B h x := by
    calc
      B x x = B x (q • h + d • K) := rfl
      _ = q * B x h + d * B x K := by rw [add_right, smul_right, smul_right]
      _ = q * B h x := by rw [hsym x h, hxK, mul_zero, add_zero]
  let y : Pic := (q + 1) • x + K
  have hyK : B y K = B K K := by simp only [y, add_left, smul_left, hxK, mul_zero, zero_add]
  refine ⟨y, ?_, ?_, hyK.trans_lt hn⟩
  · have hxy : B x y = (q + 1) * B x x := by
      simp only [y, add_right, smul_right, hxK, add_zero]
    have hyy : B y y = (q + 1) * ((q + 1) * B x x) + B K K := calc
      B y y = B ((q + 1) • x + K) y := rfl
      _ = _ := by rw [add_left, smul_left, hxy, hsym K y, hyK]
    have hlt : q < (q + 1) * ((q + 1) * (q * B h x)) := by
      have hhx₁ : 1 ≤ B h x := by omega
      have h₁ : q ≤ q * B h x := le_mul_of_one_le_right hq.le hhx₁
      have h₂ : q * B h x < (q + 1) * (q * B h x) := by
        simpa only [one_mul] using mul_lt_mul_of_pos_right
          (show (1 : ℤ) < q + 1 by omega) (mul_pos hq hhx)
      have h₃ : (q + 1) * (q * B h x) ≤ (q + 1) * ((q + 1) * (q * B h x)) := by
        exact le_mul_of_one_le_left (mul_nonneg (by omega) (mul_pos hq hhx).le) (by omega)
      exact h₁.trans_lt (h₂.trans_le h₃)
    rw [hyy, hxx]
    have h : -(B K K) < (q + 1) * ((q + 1) * (q * B h x)) := hlt
    omega
  · simp only [y, add_right, smul_right]
    exact add_pos_of_pos_of_nonneg (mul_pos (by omega) hhx) hd₀

include rational in
private theorem exists_effectiveClass_of_canonical_degree_neg (hK : B K K ≤ 0) :
    ∃ a : Pic, a ∈ E ∧ B a K < 0 := by
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  let h : Pic := Additive.ofMul H
  have hh : 0 < B h h := by
    simpa only [h, intersectionBilinForm_apply, toMul_ofMul] using
      classIntersectionNumber_pos_of_isAmple k dim₂ hH hH
  suffices ∃ a : Pic, 0 < B a a ∧ 0 < B h a ∧ B a K < 0 by
    obtain ⟨a, haa, hha, haK⟩ := this
    simp only [intersectionBilinForm_apply, h, toMul_ofMul] at haa hha
    obtain ⟨n, hn, I, hI, he⟩ :=
      (eventually_exists_effectiveCartier_pow_of_positive_cone k a.toMul hH haa hha).exists
    refine ⟨n • a, mem_effectiveClasses.mpr
      ⟨hI.toCartierDivisor, hI.isEffective_toCartierDivisor, by
        rw [hI.toLineBundleClass_toCartierDivisor, he, ofMul_pow, ofMul_toMul]⟩, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_left]
    exact mul_neg_of_pos_of_neg (Int.natCast_pos.mpr hn) haK
  by_cases hneg : B h K < 0
  · exact ⟨h, hh, hh, hneg⟩
  have hkne : K ≠ (0 : Pic) := by
    intro hz
    exact two_nsmul_canonical_notMem_effectiveClasses (k := k) (X := X)
      (by rw [hz, nsmul_zero]; exact (X.effectiveClasses).zero_mem)
  have hn : B K K < 0 := by
    by_contra! hzero
    have heq := le_antisymm hK hzero
    have hA := anticanonical_mem_effectiveClasses k heq.ge
    have hpos := intersection_pos_of_mem_effectiveClasses k (h := h) hH hA (neg_ne_zero.mpr hkne)
    rw [map_neg] at hpos
    omega
  exact exists_positive_class_of_canonical_square_neg k hh (le_of_not_gt hneg) hn

include rational in
private theorem exists_primeDivisorClass_notMem_zmultiples_canonical :
    ∃ p : CodimensionOnePoint X, P(p) ∉ AddSubgroup.zmultiples K := by
  by_contra! h
  apply X.not_surjective_zpow_canonicalBundle_of_isRationalOver k
  intro a
  obtain ⟨D, hD⟩ := weilToLineBundleClassHom_surjective (X := X) (Additive.ofMul a)
  have hd : cl D ∈ AddSubgroup.zmultiples K := by
    rw [← Finsupp.sum_single D, map_finsuppSum, Finsupp.sum]
    refine AddSubgroup.sum_mem _ fun p _ ↦ ?_
    rw [weilToLineBundleClassHom_single, ← primeDivisorClass_def]
    exact AddSubgroup.zsmul_mem _ (h p) _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hD ▸ hd)
  exact ⟨n, by simpa only [toMul_zsmul, toMul_ofMul] using congrArg Additive.toMul hn⟩

include rational in
private theorem self_add_canonical_degree_eq_neg_two_of_adjoint_notMem_effectiveClasses
    (p : CodimensionOnePoint X) (hnot : K + P(p) ∉ E) :
    B P(p) P(p) + B P(p) K = -2 := by
  have hsym : B K P(p) = B P(p) K := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  have hχ : 2 * (eulerCharBelow k (K + P(p)).toMul 3 - 1) =
      B (K + P(p)) (K + P(p)) - B (K + P(p)) K := by
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      eulerCharBelow_eq_riemannRoch_of_isRationalOver k (K + P(p)).toMul
  simp only [add_left, add_right, hsym] at hχ
  let I := C(p)
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : Module.Finite k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) :=
    moduleFinite_cohomology_of_isProjectiveOver k (InvertibleSheaf.trivial I.subscheme).obj 1
  have hadj : 2 * (I.subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B P(p) K := by
    simpa only [I, intersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  by_contra! hne
  rcases mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos k (K + P(p)) (by omega)
    with h | h
  · exact hnot h
  · have hneg : -P(p) ∈ E := by simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using h
    obtain ⟨H, hh⟩ := X.exists_isAmple_of_isProjectiveOver k
    have hnef : H.IsNef k f := (isNef_iff_classIntersectionNumber_nonneg k dim₂ _).mpr
      fun q ↦ (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hh q).le
    have hc := intersection_nonneg_of_mem_effectiveClasses k (h := Additive.ofMul H) hnef hneg
    rw [neg_right, intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul, neg_nonneg] at hc
    exact (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hh p).not_ge hc

omit algClosed [X.IsProjectiveOver k] rational [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
private theorem adjoint_notMem_effectiveClasses_of_sub_mem {a b : Pic}
    (ha : K + a ∉ E) (hab : a - b ∈ E) : K + b ∉ E := fun h ↦ ha (by
  have hsum := (X.effectiveClasses).add_mem hab h
  rwa [show a - b + (K + b) = K + a by abel] at hsum)

include rational in
private theorem canonical_degree_neg_of_irreducible_anticanonical
    (hK : 0 < B K K) {haK : -K ∈ E} (hprime : AddIrreducible (⟨-K, haK⟩ : E))
    (p : CodimensionOnePoint X) (hp : B K P(p) ≤ 0) (hnot : K + P(p) ∉ E) :
    B P(p) K < 0 := by
  have hsym : B P(p) K = B K P(p) := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  rw [hsym]
  by_contra! h
  have hzero : B K P(p) = 0 := le_antisymm hp h
  have hs := self_add_canonical_degree_eq_neg_two_of_adjoint_notMem_effectiveClasses k p hnot
  rw [hsym, hzero] at hs
  -- A component of canonical degree zero would split the anticanonical class.
  have hRR : 2 * (eulerCharBelow k (-K - P(p)).toMul 3 - 1) =
      B (-K - P(p)) (-K - P(p)) - B (-K - P(p)) K := by
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      eulerCharBelow_eq_riemannRoch_of_isRationalOver k (-K - P(p)).toMul
  simp only [map_sub, LinearMap.sub_apply, neg_left, neg_right, hsym, hzero] at hRR
  rcases mem_effectiveClasses_or_canonical_sub_of_eulerChar_pos k (-K - P(p)) (by omega)
    with hrest | htwo
  · have hd : (⟨-K, haK⟩ : E) = ⟨P(p), primeDivisorClass_mem_effectiveClasses p⟩ +
        ⟨-K - P(p), hrest⟩ := Subtype.ext (by simp)
    rcases hprime.isAddUnit_or_isAddUnit hd with hr' | hs'
    · have he := congrArg Subtype.val
        ((isAddUnit_effectiveClasses_iff_eq_zero k dim₂ _).mp hr')
      have hz : P(p) = (0 : Pic) := he
      simp only [hz, zero_left, zero_add] at hs
      omega
    · have he := congrArg Subtype.val
        ((isAddUnit_effectiveClasses_iff_eq_zero k dim₂ _).mp hs')
      have hz : -K - P(p) = (0 : Pic) := he
      have hbad := congrArg (B K) (sub_eq_zero.mp hz)
      rw [map_neg, hzero] at hbad
      omega
  · exact hnot (by
      have ht := (X.effectiveClasses).add_mem haK htwo
      rwa [show -K + (K - (-K - P(p))) = K + P(p) by abel] at ht)

include rational in
private theorem exists_prime_with_ineffective_adjoint_of_irreducible_anticanonical
    (hK : 0 < B K K) {haK : -K ∈ E} (hprime : AddIrreducible (⟨-K, haK⟩ : E)) :
    ∃ p : CodimensionOnePoint X, B P(p) K < 0 ∧ K + P(p) ∉ E := by
  obtain ⟨p, hp⟩ := exists_primeDivisorClass_eq_of_addIrreducible k dim₂ _ hprime
  have heq : P(p) = -K := hp
  have hnn : 0 ≤ B P(p) P(p) := by
    rw [heq, neg_left, neg_right, neg_neg]
    exact hK.le
  have hn : (-K : Pic).toMul.IsNef k f := heq ▸ isNef_primeDivisorClass_of_self_nonneg k p hnn
  have hneg : B (-K) K < 0 := by simpa only [neg_left, neg_lt_zero] using hK
  obtain ⟨q, hq⟩ := exists_primeDivisorClass_notMem_zmultiples_canonical (k := k) (X := X)
  obtain ⟨n, hn₁, hn₂⟩ := exists_last_effective_adjoint k hn hneg
    (primeDivisorClass_mem_effectiveClasses q)
  let c := P(q) + n • K
  have hnonzero : c ≠ 0 := by
    intro hc
    apply hq
    rw [show P(q) = -(n • K) from eq_neg_of_add_eq_zero_left hc]
    exact (AddSubgroup.zmultiples K).neg_mem ((AddSubgroup.zmultiples K).nsmul_mem
      (AddSubgroup.mem_zmultiples K) n)
  have hnonpos : B K c ≤ 0 := by
    simpa only [neg_left, neg_nonneg] using
      intersection_nonneg_of_mem_effectiveClasses k hn (a := c) hn₁
  obtain ⟨r, hr, -, hres⟩ := exists_component_of_intersection_nonpos k hn₁ hnonzero hnonpos
  have hn₃ : K + c ∉ E := by
    rw [show K + c = P(q) + (n + 1) • K by simp only [c, add_nsmul, one_nsmul]; abel]
    exact hn₂
  have hnot := adjoint_notMem_effectiveClasses_of_sub_mem k hn₃ hres
  exact ⟨r, canonical_degree_neg_of_irreducible_anticanonical k hK hprime r hr hnot, hnot⟩

include rational in
private theorem exists_class_of_canonical_degree_neg_of_canonical_square_pos (hK : 0 < B K K) :
    ∃ a : Pic, a ∈ E ∧ B a K < 0 ∧ K + a ∉ E := by
  have haK := anticanonical_mem_effectiveClasses k hK.le
  let aK : E := ⟨-K, haK⟩
  have hkne : K ≠ (0 : Pic) := by
    intro hz
    simp [hz] at hK
  have hu : ¬ IsAddUnit aK :=
    fun h ↦ (neg_ne_zero.mpr hkne) (congrArg Subtype.val
      ((isAddUnit_effectiveClasses_iff_eq_zero k dim₂ aK).mp h))
  rcases addIrreducible_or_factor hu with hprime | ⟨a, b, ha, hb, hab⟩
  · obtain ⟨p, hp, hnot⟩ := exists_prime_with_ineffective_adjoint_of_irreducible_anticanonical
      k hK hprime
    exact ⟨P(p), primeDivisorClass_mem_effectiveClasses p, hp, hnot⟩
  · have hsum : -K = a.val + b.val := congrArg Subtype.val hab
    have hpair := congrArg (B K) hsum
    simp only [map_add, map_neg] at hpair
    suffices ∀ a b : E, ¬ IsAddUnit b → -K = a.val + b.val → B K a.val < 0 →
        ∃ c : Pic, c ∈ E ∧ B c K < 0 ∧ K + c ∉ E by
      by_cases hneg : B K a.val < 0
      · exact this a b hb hsum hneg
      · exact this b a ha (by simpa only [add_comm] using hsum) (by omega)
    intro a b hb hsum hneg
    refine ⟨a, a.property, ?_, fun h ↦ ?_⟩
    · simpa only [intersectionBilinForm_apply, classIntersectionNumber_comm] using hneg
    · have he : K + a.val = -b.val := by
        rw [eq_neg_iff_add_eq_zero, add_assoc, ← hsum, add_neg_cancel]
      exact hb (IsAddUnit.of_add_eq_zero ⟨-b.val, he ▸ h⟩ (Subtype.ext (add_neg_cancel _)))

include rational in
private theorem primeDivisorClass_self_nonneg_of_canonical_degree_neg
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    (p : CodimensionOnePoint X) (hp : B P(p) K < 0) : 0 ≤ B P(p) P(p) := by
  by_contra! hneg
  let I := C(p)
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  have : Module.Finite k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) :=
    moduleFinite_cohomology_of_isProjectiveOver k (InvertibleSheaf.trivial I.subscheme).obj 1
  have hadj : 2 * (I.subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B P(p) K := by
    simpa only [I, intersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hsq : B P(p) P(p) = -1 := by omega
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  apply hmin I
  refine (hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    (k := k) (dim₂).le).mpr ⟨?_, ?_⟩
  · omega
  · simpa only [intersectionBilinForm_apply, toMul_ofMul, primeDivisorClass_def] using hsq

include rational in
private theorem exists_class_of_canonical_degree_neg_of_canonical_square_nonpos
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    (hK : B K K ≤ 0) : ∃ a : Pic, a ∈ E ∧ B a K < 0 ∧ K + a ∉ E := by
  obtain ⟨a, ha, haK⟩ := exists_effectiveClass_of_canonical_degree_neg (X := X) k hK
  have hsym (b : Pic) : B K b = B b K := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  obtain ⟨p, -, hp, -⟩ := exists_component_of_intersection_nonpos k ha
    (fun he ↦ by simp [he] at haK) (by rw [hsym]; exact haK.le)
  have hneg : B P(p) K < 0 := by
    rw [← hsym]
    exact hp (by rwa [hsym])
  have hn := isNef_primeDivisorClass_of_self_nonneg k p
    (primeDivisorClass_self_nonneg_of_canonical_degree_neg k hmin p hneg)
  obtain ⟨n, hn₁, hn₂⟩ := exists_last_effective_adjoint k hn hneg
    (primeDivisorClass_mem_effectiveClasses p)
  refine ⟨P(p) + n • K, hn₁, ?_, ?_⟩
  · rw [add_left, ← Nat.cast_smul_eq_nsmul ℤ, smul_left]
    exact add_neg_of_neg_of_nonpos hneg (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hK)
  · rwa [show K + (P(p) + n • K) = P(p) + (n + 1) • K by
      simp only [add_nsmul, one_nsmul]; abel]

end Integral

variable (X) in
include rational in
/-- A smooth projective rational surface without exceptional curves of the first kind
contains an integral Cartier curve isomorphic over the ground field to the projective
line, with nonnegative self-intersection. -/
theorem exists_rational_curve_self_intersection_nonneg
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier)
      (e : I.subscheme ≅ projectiveLine k), e.hom.IsOver S ∧
        0 ≤ classIntersectionNumber k X
          (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
          (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hex : ∃ a : Pic, a ∈ E ∧ B a K < 0 ∧ K + a ∉ E := by
    rcases le_or_gt (B K K) 0 with hK | hK
    · exact exists_class_of_canonical_degree_neg_of_canonical_square_nonpos k hmin hK
    · exact exists_class_of_canonical_degree_neg_of_canonical_square_pos k hK
  obtain ⟨a, ha, haK, hnot⟩ := hex
  have hsym (b : Pic) : B K b = B b K := by
    simp only [intersectionBilinForm_apply, classIntersectionNumber_comm]
  obtain ⟨p, -, hp, hres⟩ := exists_component_of_intersection_nonpos k ha
    (fun he ↦ by simp [he] at haK) (by rw [hsym]; exact haK.le)
  have hneg : B P(p) K < 0 := by
    rw [← hsym]
    exact hp (by rwa [hsym])
  have hnot' := adjoint_notMem_effectiveClasses_of_sub_mem k hnot hres
  have hnum := self_add_canonical_degree_eq_neg_two_of_adjoint_notMem_effectiveClasses k p hnot'
  let I := C(p)
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  have : Module.Finite k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) :=
    moduleFinite_cohomology_of_isProjectiveOver k (InvertibleSheaf.trivial I.subscheme).obj 1
  have hadj : 2 * (I.subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B P(p) K := by
    simpa only [I, intersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hgen : I.subscheme.genus k = 0 := by omega
  obtain ⟨e, he⟩ := genus_eq_zero_iff_exists_iso_projectiveLine.mp hgen
  refine ⟨I, hI, e, he, ?_⟩
  simpa only [intersectionBilinForm_apply, toMul_ofMul, primeDivisorClass_def] using
    primeDivisorClass_self_nonneg_of_canonical_degree_neg k hmin p hneg

end AlgebraicGeometry.Scheme
