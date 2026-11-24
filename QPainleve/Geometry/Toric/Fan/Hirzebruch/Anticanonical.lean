/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.ProperIntersection
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Curves.Morphism
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.WeilDivisor.Basic
import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf

/-!
# Complexity-zero boundaries on Hirzebruch surfaces

A reduced anticanonical divisor of complexity zero on a Hirzebruch surface has
four components. The intersection form and the distinguished invariant section
determine their classes in the fiber and section basis. In particular the
two components of fiber degree one are disjoint sections of the character ruling,
and the two vertical components are scheme-theoretic fibers.

See [Gross, Hacking and Keel, Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.SS1)
for the role of the two-fiber case in constructing toric models.
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

section Coordinates

variable {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = 4)
  {e : ℤ} (he : 0 ≤ e) {a d : ι → ℤ}
  (had : ∑ j, a j = e + 2) (hdeg : ∑ j, d j = 2)
  (ha : ∀ j, 0 ≤ a j) (hd : ∀ j, 0 ≤ d j)
  (hvertical : ∀ j, d j = 0 → 1 ≤ a j)
  (hsection : ∀ j, a j < e * d j → d j = 1 ∧ a j = 0)

include hcard he had hdeg hd hvertical hsection in
private theorem anticanonical_fiber_degree_le_one (j : ι) : d j ≤ 1 := by
  classical
  have hrest := Finset.sum_erase_add Finset.univ d (Finset.mem_univ j)
  have hnonneg := Finset.sum_nonneg (s := Finset.univ.erase j) (fun k _ ↦ hd k)
  by_contra! hj
  have hj₂ : d j = 2 := by omega
  have hz : ∑ k ∈ Finset.univ.erase j, d k = 0 := by omega
  have hrest' (k) (hk : k ∈ Finset.univ.erase j) : d k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ hd k)).mp hz k hk
  have hsum : 3 ≤ ∑ k ∈ Finset.univ.erase j, a k := calc
    3 = ∑ _k ∈ Finset.univ.erase j, (1 : ℤ) := by simp [Finset.card_erase_of_mem, hcard]
    _ ≤ ∑ k ∈ Finset.univ.erase j, a k :=
      Finset.sum_le_sum (fun k hk ↦ hvertical k (hrest' k hk))
  have hja : 2 * e ≤ a j := by
    rw [mul_comm, ← hj₂]
    exact le_of_not_gt (fun h ↦ by have := (hsection j h).1; omega)
  have := Finset.sum_erase_add Finset.univ a (Finset.mem_univ j)
  omega

include hcard he had hdeg ha hd hvertical hsection in
private theorem exists_anticanonical_coordinate_split
    (hexception : ∀ j k, a j < e * d j → a k < e * d k → j = k) :
    ∃ s t : ι, s ≠ t ∧ d s = 1 ∧ d t = 1 ∧ a s = 0 ∧ a t = e ∧
      ∀ j, j ≠ s → j ≠ t → d j = 0 ∧ a j = 1 := by
  classical
  have hdj (j) : d j = 0 ∨ d j = 1 := by
    have := anticanonical_fiber_degree_le_one hcard he had hdeg hd hvertical hsection j
    have := hd j
    omega
  let H := Finset.univ.filter (fun j ↦ d j = 1)
  have hH : H.card = 2 := by
    have hsum : ∑ j, d j = (H.card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rcases hdj j with hj | hj <;> simp [hj]
    omega
  obtain ⟨s, t, hst, hpair⟩ := Finset.card_eq_two.mp hH
  have hmem (j) : d j = 1 ↔ j = s ∨ j = t := by
    simpa [H] using (Finset.ext_iff.mp hpair j)
  have hs := (hmem s).mpr (Or.inl rfl)
  have ht := (hmem t).mpr (Or.inr rfl)
  let V := (Finset.univ.erase s).erase t
  have htV : t ∈ Finset.univ.erase s := Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ t⟩
  have hV : V.card = 2 := by simp [V, Finset.card_erase_of_mem, htV, hcard]
  have hv (j) (hj : j ∈ V) : d j = 0 := by
    rcases hdj j with hz | ho
    · exact hz
    · rcases (hmem j).mp ho with rfl | rfl <;> simp [V] at hj
  have hsumV : ∑ j ∈ V, a j + a t + a s = e + 2 := by
    rw [Finset.sum_erase_add _ _ htV, Finset.sum_erase_add _ _ (Finset.mem_univ s), had]
  have hVle : 2 ≤ ∑ j ∈ V, a j := calc
    2 = ∑ _j ∈ V, (1 : ℤ) := by simp [hV]
    _ ≤ ∑ j ∈ V, a j := Finset.sum_le_sum (fun j hj ↦ hvertical j (hv j hj))
  have hsplit : (a s = 0 ∧ a t = e) ∨ (a t = 0 ∧ a s = e) := by
    have := ha s
    have := ha t
    by_cases hse : a s < e
    · have hsz := (hsection s (by simpa [hs] using hse)).2
      by_cases hte : a t < e
      · exact (hst (hexception s t (by simpa [hs] using hse)
          (by simpa [ht] using hte))).elim
      · exact Or.inl ⟨hsz, by omega⟩
    · by_cases hte : a t < e
      · have htz := (hsection t (by simpa [ht] using hte)).2
        exact Or.inr ⟨htz, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
  have hVexact : ∑ k ∈ V, a k = 2 := by rcases hsplit with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  have hz : ∑ k ∈ V, (a k - 1) = 0 := by simp [Finset.sum_sub_distrib, hVexact, hV]
  have hout (j) (hjs : j ≠ s) (hjt : j ≠ t) : d j = 0 ∧ a j = 1 := by
    have hj : j ∈ V := by simp [V, hjs, hjt]
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk ↦
      sub_nonneg.mpr (hvertical k (hv k hk)))).mp hz j hj
    exact ⟨hv j hj, sub_eq_zero.mp hh⟩
  rcases hsplit with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨s, t, hst, hs, ht, h₁, h₂, hout⟩
  · exact ⟨t, s, hst.symm, ht, hs, h₁, h₂, fun j hjt hjs ↦ hout j hjs hjt⟩

end Coordinates

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Φ.hirzebruchPicardBasis b e hΦ r hr
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "P" p:arg =>
  Additive.ofMul
    (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ) p)
local notation "F₁" => Φ.rayBoundaryPoint hΦ (r 1)
local notation "F₃" => Φ.rayBoundaryPoint hΦ (r 3)
local notation "S₀" => Φ.rayBoundaryPoint hΦ (r 0)
local notation "K" => Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))

private theorem hirzebruch_section_coordinates :
    (C).repr (P S₀) 0 = 0 ∧ (C).repr (P S₀) 1 = 1 := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have h : C 1 = P S₀ := by
    rw [hirzebruchPicardBasis_apply_one, rayDivisorToPicard_single, one_zsmul]
  rw [← h, Basis.repr_self]
  simp

include b e hΦ r hr in
private theorem card_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero
    {D : (X).IdealSheafData} [Fintype D.boundaryPrimes] (hzero : D.boundaryComplexity = 0) :
    Fintype.card D.boundaryPrimes = 4 := by
  rw [boundaryComplexity_def, finrank_eq_card_basis C, Fintype.card_fin,
    Set.ncard_eq_toFinset_card', Set.toFinset_card] at hzero
  omega

variable [(Φ.algebraicRealization).IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

include hc in
private theorem hirzebruch_fiber_degree_nonneg (p : CodimensionOnePoint X) :
    0 ≤ (C).repr (P p) 1 := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  rw [← (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (P p)).1]
  by_cases hp : p = F₁
  · have hne : F₁ ≠ F₃ :=
      (Φ.rayBoundaryPoint_injective hΦ).ne (r.injective.ne (by decide))
    rw [hp, hirzebruchPicardBasis_apply_zero_eq_ray_three, rayDivisorToPicard_single, one_zsmul]
    simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using
      Chow.classIntersectionNumber_primeDivisorClass_nonneg_of_ne ℂ hdim hne
  · rw [hirzebruchPicardBasis_apply_zero, rayDivisorToPicard_single, one_zsmul]
    simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using
      Chow.classIntersectionNumber_primeDivisorClass_nonneg_of_ne ℂ hdim hp

include hc in
private theorem eq_section_of_hirzebruch_fiber_coeff_lt (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 0 < e * (C).repr (P p) 1) : p = S₀ := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  by_contra hn
  have hnonneg := Chow.classIntersectionNumber_primeDivisorClass_nonneg_of_ne ℂ hdim hn
  have h := (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (P p)).2
  rw [hirzebruchPicardBasis_apply_one, rayDivisorToPicard_single, one_zsmul,
    Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul] at h
  omega

include hc in
private theorem hirzebruch_fiber_coeff_nonneg (he : 0 ≤ e) (p : CodimensionOnePoint X) :
    0 ≤ (C).repr (P p) 0 := by
  by_cases hp : (C).repr (P p) 0 < e * (C).repr (P p) 1
  · rw [eq_section_of_hirzebruch_fiber_coeff_lt b e hΦ hc r hr p hp,
      (hirzebruch_section_coordinates b e hΦ r hr).1]
  · exact (mul_nonneg he (hirzebruch_fiber_degree_nonneg b e hΦ hc r hr p)).trans (le_of_not_gt hp)

include hc in
private theorem hirzebruch_fiber_coeff_pos_of_degree_zero (he : 0 ≤ e) (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 1 = 0) : 1 ≤ (C).repr (P p) 0 := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hn := hirzebruch_fiber_coeff_nonneg b e hΦ hc r hr he p
  by_contra! h
  have hz : (C).repr (P p) 0 = 0 := by omega
  have hzero : P p = 0 := by
    apply (C).repr.injective
    apply Finsupp.ext
    intro j
    fin_cases j <;> simp [hz, hp]
  obtain ⟨L, hL⟩ := (X).exists_isAmple_of_isProjectiveOver ℂ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hpos := Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple ℂ hdim hL p
  have hvanish : primeDivisorClass p = 1 := Additive.ofMul.injective hzero
  simp [hvanish, Chow.classIntersectionNumber_one_right] at hpos

include hc in
private theorem hirzebruch_anticanonical_coordinates :
    (C).repr (-K) 0 = e + 2 ∧ (C).repr (-K) 1 = 2 := by
  have hflip (j : Fin 2) : B K (C j) = B (C j) K := by
    simpa only [Chow.intersectionBilinForm_apply] using
      Chow.classIntersectionNumber_comm (k := ℂ) (K).toMul (Additive.toMul (C j))
  have hcanon (j : Fin 2) := Φ.hirzebruchPicardBasis_intersection_canonical b e hΦ r hr hc j
  have hd := (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc K).1
  have ha := (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc K).2
  rw [hflip, hcanon] at hd ha
  have h₁ : (C).repr K 1 = -2 := by simpa using hd.symm
  have h₀ : (C).repr K 0 = -e - 2 := by rw [h₁] at ha; simp at ha; linarith
  simp [h₀, h₁, add_comm]

include hc in
private theorem disjoint_of_hirzebruch_section_classes (s t : CodimensionOnePoint X)
    (hne : s ≠ t) (hs : P s = C 1) (ht : P t = e • C 0 + C 1) :
    Disjoint (closure {(s : X)}) (closure {(t : X)}) := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hzero : B (P t) (P s) = 0 := by
    rw [hs, (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc _).2, ht, map_add, map_smul]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self]
    simp
  have hpos := Chow.classIntersectionNumber_primeDivisorClass_pos_iff ℂ hdim.le hne.symm
  rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul] at hzero
  exact Set.disjoint_left.mpr fun x hx hy ↦
    (lt_irrefl (0 : ℤ)) (hzero ▸ hpos.mpr ⟨x, hy, hx⟩)

omit [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))] in
include hc in
/-- A reduced anticanonical divisor of complexity zero on a Hirzebruch surface
has two components of fiber class and two of classes S and S + eF, where S
is the section of square -e and F is the fiber class. The latter two components
are disjoint. For positive index e, the component of class S is the invariant
negative section. -/
theorem exists_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero (he : 0 ≤ e)
    {D : (X).IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hzero : D.boundaryComplexity = 0) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [algebraicRealization_over]
      exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2) →
    ∃ s t : D.boundaryPrimes, s ≠ t ∧
      P (D.boundaryPrimeEmbedding s) = C 1 ∧
      P (D.boundaryPrimeEmbedding t) = e • C 0 + C 1 ∧
      (∀ p : D.boundaryPrimes, p ≠ s → p ≠ t → P (D.boundaryPrimeEmbedding p) = C 0) ∧
      Disjoint (closure {(s : X)}) (closure {(t : X)}) ∧
      (0 < e → D.boundaryPrimeEmbedding s = S₀) := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  intro hSmooth hK
  let := hSmooth
  classical
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  let p := D.boundaryPrimeEmbedding
  let a (j : D.boundaryPrimes) := (C).repr (P (p j)) 0
  let d (j : D.boundaryPrimes) := (C).repr (P (p j)) 1
  have hcard := card_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero b e hΦ r hr hzero
  have hsum : ∑ j, P (p j) = -K := by
    rw [← hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p
      (fun q ↦ D.range_boundaryPrimeEmbedding.symm ▸ Iff.rfl), hK]
    rfl
  have hsums (j : Fin 2) : ∑ k, (C).repr (P (p k)) j = (C).repr (-K) j := by
    rw [← Finsupp.finsetSum_apply, ← map_sum, hsum]
  have ⟨hcan₀, hcan₁⟩ := hirzebruch_anticanonical_coordinates b e hΦ hc r hr
  have hsection (j : D.boundaryPrimes) (hj : a j < e * d j) : p j = S₀ :=
    eq_section_of_hirzebruch_fiber_coeff_lt b e hΦ hc r hr (p j) hj
  obtain ⟨s, t, hst, hs, ht, hsa, hta, hf⟩ :=
    exists_anticanonical_coordinate_split hcard he ((hsums 0).trans hcan₀) ((hsums 1).trans hcan₁)
      (fun j ↦ hirzebruch_fiber_coeff_nonneg b e hΦ hc r hr he (p j))
      (fun j ↦ hirzebruch_fiber_degree_nonneg b e hΦ hc r hr (p j))
      (fun j ↦ hirzebruch_fiber_coeff_pos_of_degree_zero b e hΦ hc r hr he (p j))
      (fun j hj ↦ by
        have h := hirzebruch_section_coordinates b e hΦ r hr
        exact ⟨by simpa only [d, hsection j hj] using h.2,
          by simpa only [a, hsection j hj] using h.1⟩)
      (fun j k hj hk ↦ p.injective ((hsection j hj).trans (hsection k hk).symm))
  have hrepr (j : D.boundaryPrimes) : P (p j) = a j • C 0 + d j • C 1 := by
    simpa only [Fin.sum_univ_two] using ((C).sum_repr (P (p j))).symm
  have hsClass : P (p s) = C 1 := by
    simpa only [a, d, hsa, hs, zero_smul, one_smul, zero_add] using hrepr s
  have htClass : P (p t) = e • C 0 + C 1 := by
    simpa only [a, d, hta, ht, one_smul] using hrepr t
  refine ⟨s, t, hst, hsClass, htClass, ?_, ?_, fun hpos ↦
    hsection s (by simpa only [a, d, hsa, hs, mul_one] using hpos)⟩
  · intro j hjs hjt
    obtain ⟨hj, hj'⟩ := hf j hjs hjt
    simpa only [a, d, hj, hj', zero_smul, one_smul, add_zero] using hrepr j
  · simpa only [p, D.coe_boundaryPrimeEmbedding] using
      disjoint_of_hirzebruch_section_classes b e hΦ hc r hr (p s) (p t)
        (p.injective.ne hst) hsClass htClass

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "q" =>
  Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "H" => Additive.toMul (AddEquiv.symm (projectiveLine.picardDegreeEquiv ℂ) 1)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "g[" p "]" => Scheme.IdealSheafData.subschemeι (I[p]) ≫ q

include hc in
private theorem eulerDegree_hirzebruch_ruling_prime (p : CodimensionOnePoint X) :
    eulerDegree ℂ (pullback g[p] H) = (C).repr (P p) 1 := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  rw [← intersectionNumber_def, ← intersectionNumber_pullback,
    ← Φ.hirzebruchPicardBasis_zero_eq_pullback_characterRuling b e hΦ r hr,
    ← Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber ℂ hdim,
    Chow.classIntersectionNumber_comm, ← toMul_ofMul (primeDivisorClass p),
    ← Chow.intersectionBilinForm_apply]
  exact (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (P p)).1

private theorem hirzebruch_ruling_prime_degree_of_isDominant
    (p : CodimensionOnePoint X) [IsDominant g[p]] :
    IsFinite g[p] ∧ Flat g[p] ∧
      ∀ y : projectiveLine ℂ, eulerDegree ℂ (pullback g[p] H) = (g[p].finrank y : ℤ) := by
  let Y := (I[p]).subscheme
  have : Y.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (I[p]).subschemeι
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Y.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ hdim p⟩
  let : (projectiveLine ℂ).IsCurveOver ℂ := projectiveLine.isCurveOver ℂ
  let : ∀ z : projectiveLine ℂ, ValuationRing ((projectiveLine ℂ).presheaf.stalk z) :=
    Scheme.IsCurveOver.valuationRing_stalk ℂ _
  have : IsFinite g[p] := g[p].isFinite_of_isDominant_of_isCurveOver (k := ℂ)
  have : Flat g[p] := g[p].flat_of_isDominant_of_valuationRing
  have (j : ℕ) := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver ℂ
    (InvertibleSheaf.trivial Y).obj j
  refine ⟨inferInstance, inferInstance, fun y ↦ ?_⟩
  rw [eulerDegree_pullback_of_isDominant ℂ g[p],
    g[p].finrank_eq_finrank_fieldRange_functionFieldMap]
  have hH : eulerDegree ℂ H = 1 := by
    simpa only [projectiveLine.picardDegreeEquiv_apply] using
      (projectiveLine.picardDegreeEquiv ℂ).apply_symm_apply 1
  rw [hH, mul_one]

include hc in
private theorem isIso_hirzebruch_ruling_prime_of_degree_one (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 1 = 1) : IsIso g[p] := by
  let Y := (I[p]).subscheme
  have : Y.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (I[p]).subschemeι
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Y.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ hdim p⟩
  have hdeg := (eulerDegree_hirzebruch_ruling_prime b e hΦ hc r hr p).trans hp
  have : IsDominant g[p] := by
    apply isDominant_iff_genericPoint_eq.mpr
    by_contra h
    have hd : topologicalKrullDim (projectiveLine ℂ) = 1 :=
      Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ
    have hy := TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint hd.le h
    have hrange : Subsingleton (g[p]).image := by
      constructor
      intro x y
      apply (g[p]).imageι.isEmbedding.injective
      have hr : Set.range (g[p]).imageι ⊆ {g[p] (genericPoint Y)} := by
        rw [Scheme.Hom.range_imageι]
        exact closure_minimal (Set.range_subset_iff.mpr fun z ↦
          ((genericPoint_specializes z).map (g[p]).continuous).mem_closed hy rfl) hy
      exact (hr (Set.mem_range_self x)).trans (hr (Set.mem_range_self y)).symm
    have hz := intersectionNumber_eq_zero_of_subsingleton_image (k := ℂ) H g[p] hrange
    rw [intersectionNumber_def, hdeg] at hz
    exact one_ne_zero hz
  obtain ⟨hfinite, hflat, hrank⟩ := hirzebruch_ruling_prime_degree_of_isDominant b e r hr p
  let := hfinite
  let := hflat
  refine (g[p].isIso_iff_finrank_eq).mpr (funext fun y ↦ ?_)
  exact_mod_cast (hrank y).symm.trans hdeg

private theorem eq_hirzebruch_ruling_fiber_of_prime_class_eq
    (p : CodimensionOnePoint X) (hp : P p = C 0) {y : Spec (CommRingCat.of ℂ) ⟶ projectiveLine ℂ}
    (hy : y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S) (hz : (p : X) ∈ (y.ker.comap q).support) :
    I[p] = y.ker.comap q := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hm : m ≠ 0 := by
    intro hz
    have hh := DFunLike.congr_fun hz (b 1)
    simp [Basis.coord_apply] at hh
  let hI := Φ.isEffectiveCartier_characterRuling_fiber m
    (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr) hm y hy
  have hyC := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension y hy)
    |>.isEffectiveCartier
  have hyH : (LineBundleClass.mk hyC.toInvertibleSheaf)⁻¹ = H := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv ℂ).injective
    rw [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul, projectiveLine.eulerDegree_inv,
      LineBundleClass.eulerDegree_mk, y.eulerDegree_ker_of_smooth hy]
    simp only [ofMul_toMul, AddEquiv.apply_symm_apply, neg_neg]
  have hclass : (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = (Additive.toMul (C 0)) := by
    rw [Φ.hirzebruchPicardBasis_zero_eq_pullback_characterRuling b e hΦ r hr, ← hyH, pullback_inv,
      hyC.pullback_mk_toInvertibleSheaf hI]
  let W := hI.toCartierDivisor.toWeilDivisor
  let cl := Scheme.CartierDivisor.weilToLineBundleClassHom X
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hI.isEffective_toCartierDivisor
  have hpW : 0 < W p := lt_of_le_of_ne (hW p)
    (fun h ↦ (hI.coeff_toWeilDivisor_eq_zero_iff p).mp h.symm hz)
  have hle := WeilDivisor.single_one_le_of_coeff_pos hW hpW
  have hcl : cl W = cl (Finsupp.single p 1) := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_single, one_smul, ← primeDivisorClass_def,
      hp, Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_toMul]
  have hW_eq := (Chow.weilToLineBundleClassHom_eq_zero_iff_of_nonneg ℂ hdim
    (sub_nonneg.mpr hle)).mp (by rw [map_sub, hcl, sub_self])
  refine ((hI.toCartierDivisor_eq_iff
    (isEffectiveCartier_vanishingIdeal_closure_singleton p.property)).mp ?_).symm
  apply Scheme.CartierDivisor.toWeilDivisor_injective
  rw [toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton,
    ← one_smul ℤ (WeilDivisor.ofPoint p), ← WeilDivisor.single_eq_zsmul_ofPoint]
  exact sub_eq_zero.mp hW_eq

include hc in
private theorem exists_hirzebruch_ruling_fiber_of_prime_class_eq
    (p : CodimensionOnePoint X) (hp : P p = C 0) :
    ∃ y : Spec (CommRingCat.of ℂ) ⟶ projectiveLine ℂ,
      y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ I[p] = y.ker.comap q := by
  let Y := (I[p]).subscheme
  have hdeg := eulerDegree_hirzebruch_ruling_prime b e hΦ hc r hr p
  rw [hp, Basis.repr_self] at hdeg
  have hdeg₀ : eulerDegree ℂ (pullback g[p] H) = 0 := by simpa using hdeg
  let y₀ := q (p : X)
  have hgeneric : g[p] (genericPoint Y) = y₀ := by
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_vanishingIdeal_closure_singleton]
  have hy₀ : IsClosed ({y₀} : Set (projectiveLine ℂ)) := by
    have hd : topologicalKrullDim (projectiveLine ℂ) = 1 :=
      Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ
    apply TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint hd.le
    intro hy
    have : IsDominant g[p] := isDominant_iff_genericPoint_eq.mpr (hgeneric.trans hy)
    obtain ⟨hfinite, hflat, hrank⟩ := hirzebruch_ruling_prime_degree_of_isDominant b e r hr p
    let := hfinite
    let := hflat
    have hn : g[p].finrank y₀ = 0 := by exact_mod_cast (hrank y₀).symm.trans hdeg₀
    exact ((g[p]).finrank_eq_zero_iff_notMem_range y₀).mp hn ⟨genericPoint Y, hgeneric⟩
  let y := pointOfClosedPoint (projectiveLine ℂ ↘ S) y₀ hy₀
  have hy : y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S :=
    pointOfClosedPoint_comp (projectiveLine ℂ ↘ S) y₀ hy₀
  refine ⟨y, hy, ?_⟩
  have hz : (p : X) ∈ (y.ker.comap q).support := by
    rw [← SetLike.mem_coe, support_comap, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
      Scheme.Hom.support_ker]
    exact subset_closure ⟨IsLocalRing.closedPoint ℂ, pointOfClosedPoint_apply _ _ _ _⟩
  exact eq_hirzebruch_ruling_fiber_of_prime_class_eq b e hΦ r hr p hp hy hz

include hc in
private theorem exists_ruling_fiber_pair_of_hirzebruch_boundary
    {D : (X).IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hzero : D.boundaryComplexity = 0) {s t : D.boundaryPrimes} (hst : s ≠ t)
    (hf : ∀ j : D.boundaryPrimes, j ≠ s → j ≠ t → P (D.boundaryPrimeEmbedding j) = C 0) :
    ∃ y z : Spec (CommRingCat.of ℂ) ⟶ projectiveLine ℂ,
      y (IsLocalRing.closedPoint ℂ) ≠ z (IsLocalRing.closedPoint ℂ) ∧
      y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ z ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧
      D = I[D.boundaryPrimeEmbedding s] * I[D.boundaryPrimeEmbedding t] *
        (y.ker.comap q) * (z.ker.comap q) := by
  classical
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  let p := D.boundaryPrimeEmbedding
  have hcard := card_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero b e hΦ r hr hzero
  let V : Finset D.boundaryPrimes := (Finset.univ.erase s).erase t
  have htV : t ∈ (Finset.univ.erase s : Finset D.boundaryPrimes) := by simp [hst.symm]
  have hV : V.card = 2 := by simp [V, Finset.card_erase_of_mem, htV, hcard]
  obtain ⟨u, v, huv, huvV⟩ := Finset.card_eq_two.mp hV
  have hmem (j : D.boundaryPrimes) : j ∈ V ↔ j ≠ s ∧ j ≠ t := by
    simp [V, and_comm]
  have hu := (hmem u).mp (by simp [huvV])
  have hv := (hmem v).mp (by simp [huvV])
  obtain ⟨y, hy, hY⟩ :=
    exists_hirzebruch_ruling_fiber_of_prime_class_eq b e hΦ hc r hr (p u) (hf u hu.1 hu.2)
  obtain ⟨z, hz, hZ⟩ :=
    exists_hirzebruch_ruling_fiber_of_prime_class_eq b e hΦ hc r hr (p v) (hf v hv.1 hv.2)
  have hne : y (IsLocalRing.closedPoint ℂ) ≠ z (IsLocalRing.closedPoint ℂ) := by
    intro h
    have hyz := ext_of_apply_closedPoint_eq (projectiveLine ℂ ↘ S) hy hz h
    have heq := hY.trans (hyz ▸ hZ.symm)
    have hclosures := congrArg (fun J : (X).IdealSheafData ↦ (J.support : Set X)) heq
    simp only [coe_support_vanishingIdeal, Closeds.coe_mk] at hclosures
    have hm : (p u : X) ∈ closure {(p v : X)} := by
      rw [← hclosures]
      exact subset_closure (Set.mem_singleton _)
    exact huv.symm (p.injective (CodimensionOnePoint.eq_of_specializes
      (specializes_iff_mem_closure.mpr hm)))
  refine ⟨y, z, hne, hy, hz, ?_⟩
  rw [← hY, ← hZ]
  let T := Finset.univ.map p
  have hT (a : CodimensionOnePoint X) : a ∈ T ↔ (a : X) ∈ D.support := by
    simpa [T, p, Finset.mem_map] using Set.ext_iff.mp D.range_boundaryPrimeEmbedding a
  calc
    D = ∏ j : D.boundaryPrimes, I[p j] := by
      simpa only [T, Finset.prod_map] using hD.eq_prod_vanishingIdeal_of_isReduced T hT
    _ = _ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ s), ← Finset.prod_erase_mul _ _ htV]
      have hprod : ∏ j ∈ V, I[p j] = I[p u] * I[p v] := by
        rw [huvV, Finset.prod_insert (by simpa using huv), Finset.prod_singleton]
      rw [hprod]
      dsimp only [p]
      ac_rfl

omit [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))] in
include hΦ hc in
/-- A reduced anticanonical divisor of complexity zero on a Hirzebruch surface
is the sum of two disjoint sections and two distinct fibers of the character
ruling. The sections map isomorphically to the projective line, and the
decomposition holds for the ideal sheaves of the scheme-theoretic fibers. -/
theorem exists_sections_and_fibers_of_hirzebruch_boundaryComplexity_zero (he : 0 ≤ e)
    {D : (X).IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    (hzero : D.boundaryComplexity = 0) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [algebraicRealization_over]
      exact ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2) →
    ∃ s t : D.boundaryPrimes, IsIso g[D.boundaryPrimeEmbedding s] ∧
      IsIso g[D.boundaryPrimeEmbedding t] ∧ Disjoint (closure {(s : X)}) (closure {(t : X)}) ∧
      ∃ y z : Spec (CommRingCat.of ℂ) ⟶ projectiveLine ℂ,
        y (IsLocalRing.closedPoint ℂ) ≠ z (IsLocalRing.closedPoint ℂ) ∧
        y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ z ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧
        D = I[D.boundaryPrimeEmbedding s] * I[D.boundaryPrimeEmbedding t] *
          (y.ker.comap q) * (z.ker.comap q) := by
  intro hSmooth hK
  let := hSmooth
  let p := D.boundaryPrimeEmbedding
  obtain ⟨s, t, hst, hs, ht, hf, hdisj, -⟩ :=
    Φ.exists_boundaryPrimes_of_hirzebruch_boundaryComplexity_zero b e hΦ hc r hr he hD hzero hK
  refine ⟨s, t, isIso_hirzebruch_ruling_prime_of_degree_one b e hΦ hc r hr (p s) ?_,
    isIso_hirzebruch_ruling_prime_of_degree_one b e hΦ hc r hr (p t) ?_, hdisj,
    exists_ruling_fiber_pair_of_hirzebruch_boundary b e hΦ hc r hr hD hzero hst hf⟩
  · rw [hs, Basis.repr_self]
    simp
  · rw [ht, map_add, map_smul]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self]
    simp

end TauCeti.Toric.Fan
