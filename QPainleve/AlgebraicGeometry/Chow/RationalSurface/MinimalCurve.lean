/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical

import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Effectivity
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RankOne
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RiemannRoch
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# Smooth rational curves on minimal rational surfaces

On a minimal smooth projective rational surface there is a smooth rational curve
of nonnegative square. An effective class of negative canonical degree with
ineffective canonical translate supplies such a curve by adjunction and
Riemann–Roch. This is the curve used to start the minimal rational surface
classification.

The argument follows Vakil, *Complex Algebraic Surfaces*,
[Class 16, §2][Vakil16] and [Class 17, §1][Vakil17].

[Vakil16]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
[Vakil17]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow
open TauCeti.AlgebraicGeometry.LineBundleClass TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [rational : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "Pic" => Additive (LineBundleClass X)
local notation "K" => Additive.ofMul (LineBundleClass.mk (canonicalBundle k X 2))
local notation "P(" p ")" => Additive.ofMul (primeDivisorClass (p))
local notation "J(" p ")" =>
  vanishingIdeal (X := X) (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "E" => X.effectiveClasses
local notation "dim₂" => topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
local notation "B" => classIntersectionBilinForm k dim₂
local notation "symmB" => LinearMap.BilinForm.IsSymm.eq (classIntersectionBilinForm_isSymm k dim₂)
local notation "amplePos" =>
  classIntersectionBilinForm_pos_of_isAmple_of_mem_effectiveClasses k dim₂
local notation "effectiveNonneg" => classIntersectionBilinForm_nonneg_of_mem_effectiveClasses k dim₂
local notation "minPrime" =>
  exists_primeDivisorClass_sub_mem_effectiveClasses_of_intersection_nonpos k dim₂

private local instance smoothSurface : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _

section EffectiveClasses

variable [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

include rational in
private theorem genus_eq_zero_of_canonical_add_notMem
    (H : Pic) (hH : H.toMul.IsAmple) (p : CodimensionOnePoint X) (hp : K + P(p) ∉ E) :
    let : (J(p)).subscheme.IsProjectiveOver k :=
      Scheme.IsProjectiveOver.of_isClosedImmersion k (J(p)).subschemeι
    let : Module.Finite k (Cohomology (InvertibleSheaf.trivial (J(p)).subscheme).obj 1) :=
      Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k _ _
    (J(p)).subscheme.genus k = 0 := by
  intro _ _
  have hdeg : 0 < B H P(p) := by
    simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using
      classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hH p
  have hn : -P(p) ∉ E := by
    intro hm
    have hnonneg := effectiveNonneg (fun q ↦ by
      simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using
        (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hH q).le) hm
    rw [map_neg, neg_nonneg] at hnonneg
    exact hnonneg.not_gt hdeg
  have hadj : 2 * ((J(p)).subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B P(p) K := by
    simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  by_contra! hgen
  have h := X.mem_effectiveClasses_or_canonical_sub k (K + P(p)) (by
    simp only [map_add, LinearMap.add_apply]
    rw [symmB K P(p)]
    omega)
  exact hn (by simpa only [sub_add_cancel_left] using h.resolve_left hp)

private theorem exists_mem_effectiveClasses_notMem_zmultiples_canonical :
    ∃ a ∈ E, a ∉ AddSubgroup.zmultiples K := by
  by_contra! h
  apply X.not_surjective_zpow_canonicalBundle_of_isRationalOver k
  intro a
  obtain ⟨D, hD⟩ := weilToLineBundleClassHom_surjective (X := X) (Additive.ofMul a)
  let cl := weilToLineBundleClassHom X
  have hpos : cl D⁺ ∈ AddSubgroup.zmultiples K :=
    h _ (mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨_, posPart_nonneg D, rfl⟩)
  have hneg : cl D⁻ ∈ AddSubgroup.zmultiples K :=
    h _ (mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨_, negPart_nonneg D, rfl⟩)
  have hm := (AddSubgroup.zmultiples K).sub_mem hpos hneg
  rw [← map_sub, posPart_sub_negPart, hD] at hm
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  exact ⟨n, by simpa only [toMul_zsmul, toMul_ofMul] using congrArg Additive.toMul hn⟩

private theorem canonical_degree_neg_of_addIrreducible_anticanonical
    (H : Pic) (hH : H.toMul.IsAmple) (hK : 0 < B K K) (hanti : -K ∈ E)
    (hirr : AddIrreducible (⟨-K, hanti⟩ : E)) (p : CodimensionOnePoint X)
    (hkp : B K P(p) ≤ 0) (hpn : K + P(p) ∉ E) : B K P(p) < 0 := by
  apply lt_of_le_of_ne hkp
  intro hz
  have hg := X.genus_eq_zero_of_canonical_add_notMem k H hH p hpn
  have : (J(p)).subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k (J(p)).subschemeι
  have : Module.Finite k (Cohomology (InvertibleSheaf.trivial (J(p)).subscheme).obj 1) :=
    Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k _ _
  have hadj : 2 * ((J(p)).subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B P(p) K := by
    simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  have hs : B P(p) P(p) = -2 := by
    rw [symmB K P(p)] at hz
    omega
  -- If the canonical degree is zero, Riemann–Roch splits the anticanonical class.
  have hr := X.mem_effectiveClasses_or_canonical_sub k (-K - P(p)) (by
    simp only [map_sub, LinearMap.sub_apply, map_neg, LinearMap.neg_apply,
      symmB P(p) K, hs, hz]
    omega)
  have hb : -K - P(p) ∈ E := hr.resolve_right fun hm ↦ by
    apply hpn
    convert (E).add_mem hanti hm using 1
    abel
  let prime : E := ⟨P(p), primeDivisorClass_mem_effectiveClasses p⟩
  have hfac : (⟨-K, hanti⟩ : E) = prime + ⟨_, hb⟩ :=
    Subtype.ext (by simp [prime, sub_eq_add_neg])
  rcases hirr.isAddUnit_or_isAddUnit hfac with he | he
  · have he' : P(p) = 0 :=
      congrArg Subtype.val ((isAddUnit_effectiveClasses_iff_eq_zero k dim₂ _).mp he)
    simp [he'] at hs
  · have he' : -K - P(p) = 0 :=
      congrArg Subtype.val ((isAddUnit_effectiveClasses_iff_eq_zero k dim₂ _).mp he)
    have hn := congrArg (B K) (sub_eq_zero.mp he')
    simp only [map_neg, hz] at hn
    omega

omit rational [IsNoetherian X] in
private theorem exists_mem_effectiveClasses_canonical_neg_of_anticanonical_factor
    (hK : 0 < B K K) (hanti : -K ∈ E) {b c : E}
    (hb : ¬IsAddUnit b) (hc : ¬IsAddUnit c) (hbc : (⟨-K, hanti⟩ : E) = b + c) :
    ∃ a ∈ E, B K a < 0 ∧ K + a ∉ E := by
  have pick (a b : E) (hb : ¬IsAddUnit b) (he : (⟨-K, hanti⟩ : E) = a + b) (ha : B K a.val < 0) :
      ∃ d ∈ E, B K d < 0 ∧ K + d ∉ E := by
    refine ⟨a.val, a.property, ha, fun h ↦ hb ?_⟩
    have hsum : -K = a.val + b.val := congrArg Subtype.val he
    have heq : K + a.val = -b.val := by
      rw [eq_neg_iff_add_eq_zero, add_assoc, ← hsum, add_neg_cancel]
    exact ⟨⟨b, ⟨-b.val, heq ▸ h⟩, Subtype.ext (add_neg_cancel _),
      Subtype.ext (neg_add_cancel _)⟩, rfl⟩
  have hsum : -K = b.val + c.val := congrArg Subtype.val hbc
  have h := congrArg (B K) hsum
  simp only [map_neg, map_add] at h
  by_cases hneg : B K b.val < 0
  · exact pick b c hc hbc hneg
  · exact pick c b hb (hbc.trans (add_comm _ _)) (by omega)

private theorem exists_mem_effectiveClasses_canonical_neg_of_canonical_square_pos
    (H : Pic) (hH : H.toMul.IsAmple) (hK : 0 < B K K) :
    ∃ a ∈ E, B K a < 0 ∧ K + a ∉ E := by
  have hanti := X.anticanonical_mem_effectiveClasses k
    (by simpa only [intersectionBilinForm_apply, classIntersectionBilinForm_apply] using hK.le)
  have hanti_ne : (-K : Pic) ≠ 0 := by
    intro hz
    have h := (map_neg (B K) K).symm.trans (congrArg (B K) hz)
    simp only [map_zero, neg_eq_zero] at h
    exact hK.ne' h
  let v : E := ⟨-K, hanti⟩
  have hunit (a : E) : IsAddUnit a ↔ a = 0 :=
    isAddUnit_effectiveClasses_iff_eq_zero k dim₂ a
  rcases addIrreducible_or_factor (p := v) (fun h ↦ hanti_ne (congrArg Subtype.val
    ((hunit v).mp h))) with hirr | ⟨b, c, hb, hc, hbc⟩
  · obtain ⟨q, hq⟩ := exists_primeDivisorClass_eq_of_addIrreducible k dim₂ v hirr
    have hq' : P(q) = -K := hq
    have hnef (a : Pic) (ha : a ∈ E) : 0 ≤ B (-K) a := by
      rw [← hq']
      apply classIntersectionBilinForm_prime_nonneg_of_self_nonneg k dim₂ _ ha
      simpa only [hq', map_neg, LinearMap.neg_apply, neg_neg] using hK.le
    have hHK : B H K < 0 := by
      have h := amplePos hH hanti hanti_ne
      simpa only [map_neg, neg_pos] using h
    obtain ⟨a, ha, han⟩ := X.exists_mem_effectiveClasses_notMem_zmultiples_canonical k
    obtain ⟨n, hn, hnext⟩ := exists_last_effective_add_nsmul k dim₂
      (b := K) hH.isNef (by simpa only [classIntersectionBilinForm_apply] using hHK) ha
    have hns : K + (a + n • K) ∉ E := by
      simpa only [succ_nsmul, add_assoc, add_left_comm, add_comm] using hnext
    let d := a + n • K
    have hd : d ≠ 0 := by
      intro hz
      have hm : d ∈ AddSubgroup.zmultiples K := hz ▸ (AddSubgroup.zmultiples K).zero_mem
      have hs := (AddSubgroup.zmultiples K).sub_mem hm
        ((AddSubgroup.zmultiples K).nsmul_mem (AddSubgroup.mem_zmultiples K) n)
      exact han (by simpa only [d, add_sub_cancel_right] using hs)
    have hkd : B K d ≤ 0 := by
      simpa only [map_neg, LinearMap.neg_apply, neg_nonneg] using hnef d hn
    obtain ⟨p, hp, hkp, _⟩ := minPrime hn hd hkd
    have hpn : K + P(p) ∉ E := notMem_effectiveClasses_add_of_sub_mem hns hp
    exact ⟨P(p), primeDivisorClass_mem_effectiveClasses p,
      X.canonical_degree_neg_of_addIrreducible_anticanonical k H hH hK hanti hirr p hkp hpn, hpn⟩
  · exact X.exists_mem_effectiveClasses_canonical_neg_of_anticanonical_factor
      k hK hanti hb hc hbc

private theorem prime_self_nonneg_of_canonical_neg
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind)
    (p : CodimensionOnePoint X) (hp : B K P(p) < 0) : 0 ≤ B P(p) P(p) := by
  let I := J(p)
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  have : Module.Finite k (Cohomology (InvertibleSheaf.trivial I.subscheme).obj 1) :=
    Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver k _ _
  have hadj : 2 * (I.subscheme.genus k : ℤ) - 2 = B P(p) P(p) + B K P(p) := by
    rw [symmB K P(p)]
    simpa only [I, classIntersectionBilinForm_apply, toMul_ofMul] using
      two_mul_genus_sub_two_eq_intersection_primeDivisorClass k p
  by_contra! hn
  have he := hI.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
    (k := k) (dim₂).le
  refine hmin I (he.mpr ⟨by omega, ?_⟩)
  have hs : B P(p) P(p) = -1 := by omega
  simpa only [classIntersectionBilinForm_apply, toMul_ofMul, primeDivisorClass_def, I] using hs

private theorem exists_mem_effectiveClasses_canonical_neg_of_canonical_square_nonpos
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind) (hK : B K K ≤ 0) :
    ∃ a ∈ E, B K a < 0 ∧ K + a ∉ E := by
  obtain ⟨a, ha, haK⟩ := X.exists_effectiveClass_of_canonical_degree_neg k
    (by simpa only [intersectionBilinForm_apply, classIntersectionBilinForm_apply] using hK)
  have hka : B K a < 0 := by
    rw [symmB K a]
    simpa only [intersectionBilinForm_apply, classIntersectionBilinForm_apply] using haK
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simp at hka
  obtain ⟨p, _, _, hp⟩ := minPrime ha ha₀ hka.le
  have hp' := hp hka
  have hsq := X.prime_self_nonneg_of_canonical_neg k hmin p hp'
  have hnef := isNef_primeDivisorClass_of_self_nonneg k dim₂ p
    (by simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using hsq)
  have hpK : B P(p) K < 0 := symmB P(p) K ▸ hp'
  obtain ⟨n, hn, hnext⟩ := exists_last_effective_add_nsmul k dim₂
    (b := K) hnef (by simpa only [classIntersectionBilinForm_apply, toMul_ofMul] using hpK)
    (primeDivisorClass_mem_effectiveClasses p)
  refine ⟨P(p) + n • K, hn, ?_, ?_⟩
  · rw [map_add, map_nsmul, nsmul_eq_mul]
    exact add_neg_of_neg_of_nonpos hp' (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hK)
  · simpa only [succ_nsmul, add_assoc, add_left_comm, add_comm] using hnext

end EffectiveClasses

include rational in
/-- A smooth projective rational surface without an exceptional curve of the first kind
contains an effective Cartier curve isomorphic over the base field to the projective
line and having nonnegative self-intersection. -/
theorem exists_smooth_rational_curve_self_nonneg
    (hmin : ∀ I : X.IdealSheafData, ¬ I.IsExceptionalCurveOfFirstKind) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      0 ≤ Chow.classIntersectionNumber k X (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ ∧
      ∃ e : I.subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  have : IsIntegral X := rational.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨a, ha, hka, hnot⟩ : ∃ a ∈ E, B K a < 0 ∧ K + a ∉ E := by
    rcases le_or_gt (B K K) 0 with h | h
    · exact X.exists_mem_effectiveClasses_canonical_neg_of_canonical_square_nonpos k hmin h
    · exact X.exists_mem_effectiveClasses_canonical_neg_of_canonical_square_pos
        k (Additive.ofMul A) hA h
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simp at hka
  obtain ⟨p, hp, _, hpn⟩ := minPrime ha ha₀ hka.le
  have hg := X.genus_eq_zero_of_canonical_add_notMem k (Additive.ofMul A) hA p
    (notMem_effectiveClasses_add_of_sub_mem hnot hp)
  let I := J(p)
  have hI : I.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k dim₂ p⟩
  refine ⟨I, hI, ?_, genus_eq_zero_iff_exists_iso_projectiveLine.mp hg⟩
  simpa only [classIntersectionBilinForm_apply, toMul_ofMul, primeDivisorClass_def, I] using
    X.prime_self_nonneg_of_canonical_neg k hmin p (hpn hka)

end AlgebraicGeometry.Scheme
