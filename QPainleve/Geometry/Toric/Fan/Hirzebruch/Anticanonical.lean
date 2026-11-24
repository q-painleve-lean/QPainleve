/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Prime

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
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
local notation "P" p:arg =>
  Additive.ofMul
    (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ) p)
local notation "S₀" => Φ.rayBoundaryPoint hΦ (r 0)
local notation "K" => Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2))

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
/-- The prime coordinates of a reduced anticanonical divisor sum to the
anticanonical coordinates in the Hirzebruch fiber–section basis. -/
theorem sum_hirzebruch_boundary_prime_coordinates
    {D : (X).IdealSheafData} [IsReduced D.subscheme] [Fintype D.boundaryPrimes]
    (hD : D.IsEffectiveCartier)
    (hK : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk (QPainleve.canonicalBundle ℂ X 2)) (j : Fin 2) :
    ∑ k : D.boundaryPrimes, (C).repr (P (D.boundaryPrimeEmbedding k)) j =
      (![e + 2, 2] : Fin 2 → ℤ) j := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hsum : ∑ k : D.boundaryPrimes, P (D.boundaryPrimeEmbedding k) = -K := by
    rw [← hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass D.boundaryPrimeEmbedding
      (fun q ↦ D.range_boundaryPrimeEmbedding.symm ▸ Iff.rfl), hK]
    rfl
  rw [← Finsupp.finsetSum_apply, ← map_sum, hsum]
  obtain ⟨h₀, h₁⟩ := hirzebruch_anticanonical_coordinates b e hΦ r hr hc
  fin_cases j
  · simpa using h₀
  · simpa using h₁

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
  have hsums (j : Fin 2) := sum_hirzebruch_boundary_prime_coordinates b e hΦ hc r hr hD hK j
  have hsection (j : D.boundaryPrimes) (hj : a j < e * d j) : p j = S₀ :=
    eq_section_of_hirzebruch_fiber_coeff_lt b e hΦ r hr hc (p j) hj
  obtain ⟨s, t, hst, hs, ht, hsa, hta, hf⟩ :=
    exists_anticanonical_coordinate_split (a := a) (d := d) hcard he (hsums 0) (hsums 1)
      (fun j ↦ hirzebruch_fiber_coeff_nonneg b e hΦ r hr hc he (p j))
      (fun j ↦ hirzebruch_fiber_degree_nonneg b e hΦ r hr hc (p j))
      (fun j ↦ hirzebruch_fiber_coeff_pos_of_degree_zero b e hΦ r hr hc he (p j))
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
      disjoint_of_hirzebruch_section_classes b e hΦ r hr hc (p s) (p t)
        (p.injective.ne hst) hsClass htClass

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "q" =>
  Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "g[" p "]" => Scheme.IdealSheafData.subschemeι (I[p]) ≫ q

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
  obtain ⟨y, hy, -, hY⟩ :=
    exists_hirzebruch_ruling_fiber_of_degree_zero b e hΦ hc r hr (p u) (by
      rw [hf u hu.1 hu.2, Basis.repr_self]
      simp)
  obtain ⟨z, hz, -, hZ⟩ :=
    exists_hirzebruch_ruling_fiber_of_degree_zero b e hΦ hc r hr (p v) (by
      rw [hf v hv.1 hv.2, Basis.repr_self]
      simp)
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
