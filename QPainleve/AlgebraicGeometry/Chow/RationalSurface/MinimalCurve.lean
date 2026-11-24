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
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RankOne
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.RiemannRoch
import QPainleve.AlgebraicGeometry.Curves.GenusZero
import QPainleve.AlgebraicGeometry.LineBundle.Ample

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

variable [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

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
    have hc : 0 ≤ B (Additive.ofMul H) (-P(p)) := by
      simpa only [intersectionBilinForm_apply, toMul_ofMul] using
        intersection_nonneg_of_mem_effectiveClasses k dim₂ hnef hneg
    rw [neg_right, intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul, neg_nonneg] at hc
    exact (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k dim₂ hh p).not_ge hc

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
  have hn : (-K : Pic).toMul.IsNef k f :=
    heq ▸ isNef_primeDivisorClass_of_self_nonneg k dim₂ p
      (by simpa only [intersectionBilinForm_apply, toMul_ofMul] using hnn)
  have hneg : B (-K) K < 0 := by simpa only [neg_left, neg_lt_zero] using hK
  obtain ⟨q, hq⟩ := exists_primeDivisorClass_notMem_zmultiples_canonical (k := k) (X := X)
  obtain ⟨n, hn₁, hn₂⟩ := exists_last_effective_add_nsmul k dim₂ (b := K) hn
    (by simpa only [intersectionBilinForm_apply] using hneg)
    (primeDivisorClass_mem_effectiveClasses q)
  let c := P(q) + n • K
  have hnonzero : c ≠ 0 := by
    intro hc
    apply hq
    rw [show P(q) = -(n • K) from eq_neg_of_add_eq_zero_left hc]
    exact (AddSubgroup.zmultiples K).neg_mem ((AddSubgroup.zmultiples K).nsmul_mem
      (AddSubgroup.mem_zmultiples K) n)
  have hnonneg : 0 ≤ B (-K) c := by
    simpa only [intersectionBilinForm_apply] using
      intersection_nonneg_of_mem_effectiveClasses k dim₂ hn hn₁
  have hnonpos : B K c ≤ 0 := by simpa only [neg_left, neg_nonneg] using hnonneg
  obtain ⟨r, hr, -, hres⟩ := exists_component_of_intersection_nonpos k dim₂
    (b := (K : Pic).toMul) hn₁ hnonzero (by simpa only [intersectionBilinForm_apply] using hnonpos)
  have hn₃ : K + c ∉ E := by
    rw [show K + c = P(q) + (n + 1) • K by simp only [c, add_nsmul, one_nsmul]; abel]
    exact hn₂
  have hnot := notMem_effectiveClasses_add_of_sub_mem hn₃ hres
  exact ⟨r, canonical_degree_neg_of_irreducible_anticanonical k hK hprime r
    (by simpa only [intersectionBilinForm_apply, toMul_ofMul] using hr) hnot, hnot⟩

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
  have hKa : B K a < 0 := by rwa [hsym]
  simp only [intersectionBilinForm_apply] at hKa
  obtain ⟨p, -, hp, -⟩ := exists_component_of_intersection_nonpos k dim₂ ha
    (fun he ↦ by simp [he] at haK) hKa.le
  have hneg : B P(p) K < 0 := by
    rw [← hsym]
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using hp hKa
  have hn := isNef_primeDivisorClass_of_self_nonneg k dim₂ p
    (by simpa only [intersectionBilinForm_apply, toMul_ofMul] using
      primeDivisorClass_self_nonneg_of_canonical_degree_neg k hmin p hneg)
  obtain ⟨n, hn₁, hn₂⟩ := exists_last_effective_add_nsmul k dim₂ (b := K) hn
    (by simpa only [intersectionBilinForm_apply, toMul_ofMul] using hneg)
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
  have hKa : B K a < 0 := by rwa [hsym]
  simp only [intersectionBilinForm_apply] at hKa
  obtain ⟨p, -, hp, hres⟩ := exists_component_of_intersection_nonpos k dim₂ ha
    (fun he ↦ by simp [he] at haK) hKa.le
  have hneg : B P(p) K < 0 := by
    rw [← hsym]
    simpa only [intersectionBilinForm_apply, toMul_ofMul] using hp hKa
  have hnot' := notMem_effectiveClasses_add_of_sub_mem hnot hres
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
