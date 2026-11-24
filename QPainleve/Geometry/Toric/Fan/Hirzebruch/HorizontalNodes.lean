/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Anticanonical
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Horizontal nodes of a Hirzebruch boundary

For a numbered nodal anticanonical cycle on a Hirzebruch surface, a component
has positive fiber degree if it is horizontal. The nodes between horizontal
branches are the centers used to increase the number of boundary fibers by
elementary transformation. The incidence count includes a self-node as one node.

See [Gross, Hacking and Keel, Proposition 1.3][GHK] for the ruled boundary
reduction and its two terminal configurations.

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

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
local notation "deg" p:arg => Basis.repr C (P p) (1 : Fin 2)
local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "hR" => nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
local notation "ruling" => Φ.characterRuling m hR
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)

variable [(Φ.algebraicRealization).IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

include hc in
/-- Distinct prime curves of fiber degree zero have disjoint supports. -/
theorem disjoint_of_hirzebruch_fiber_degree_eq_zero {p q : CodimensionOnePoint X}
    (hpq : p ≠ q) (hp : deg p = 0) (hq : deg q = 0) :
    Disjoint (closure {(p : X)}) (closure {(q : X)}) := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hq' : P q = (C).repr (P q) 0 • C 0 := by
    simpa only [Fin.sum_univ_two, hq, zero_smul, add_zero] using ((C).sum_repr (P q)).symm
  have hz : B (P p) (P q) = 0 := by
    calc
      B (P p) (P q) = B (P p) ((C).repr (P q) 0 • C 0) := congrArg (B (P p)) hq'
      _ = 0 := by rw [map_smul, (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc _).1,
        hp, smul_zero]
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul] at hz
  refine Set.disjoint_left.mpr fun x hx hy ↦ ?_
  exact ((Chow.classIntersectionNumber_primeDivisorClass_pos_iff ℂ hdim.le hpq).mpr
    ⟨x, hx, hy⟩).ne' hz

include hc in
/-- A prime curve contained in a rational fiber of the Hirzebruch ruling has
fiber degree zero. -/
theorem hirzebruch_fiber_degree_eq_zero_of_mem_ruling_fiber {p : CodimensionOnePoint X}
    {y : S ⟶ projectiveLine ℂ} (hy : y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S)
    (hp : (p : X) ∈ (y.ker.comap ruling).support) : deg p = 0 := by
  let f := (I[p]).subschemeι ≫ ruling
  have : IsClosedImmersion y := y.isClosedImmersion_of_comp_eq_id hy
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let : (I[p]).subscheme.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (I[p]).subschemeι
  let : (I[p]).subscheme.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ hdim p⟩
  have hsub : Set.range f ⊆ Set.range y := by
    rintro _ ⟨x, rfl⟩
    have hmem : (I[p]).subschemeι x ∈ (y.ker.comap ruling).support := by
      apply closure_minimal (Set.singleton_subset_iff.mpr hp)
        ((y.ker.comap ruling).support).isClosed'
      simpa only [range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk]
        using Set.mem_range_self (f := (I[p]).subschemeι) x
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      y.support_ker, y.isClosedEmbedding.isClosed_range.closure_eq] at hmem
    exact hmem
  have himage : Set.range f.imageι ⊆ Set.range y := by
    rw [f.range_imageι]
    exact closure_minimal hsub y.isClosedEmbedding.isClosed_range
  have hf : Subsingleton f.image := ⟨fun x z ↦ f.imageι.injective
    (Set.subsingleton_range y (himage (Set.mem_range_self x)) (himage (Set.mem_range_self z)))⟩
  rw [← Φ.eulerDegree_hirzebruch_ruling_prime b e hΦ hc r hr p, ← intersectionNumber_def]
  exact intersectionNumber_eq_zero_of_subsingleton_image _ f hf

variable {D : Φ.algebraicRealization.IdealSheafData}
  [D.subscheme.Over (Spec (.of ℂ))] [PrestableFamily (D.subscheme ↘ Spec (.of ℂ))]
  {ι : Type*} {p : ι → (D.subscheme ↘ Spec (.of ℂ)).smoothLocus} {n : ℕ} [NeZero n]
  (A : Scheme.NodalCycleNumbering p n) (hD : D.IsEffectiveCartier)

local notation "prime[" j "]" => D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)
local notation "d[" j "]" => deg (prime[j])
local notation "vertical" => Finset.univ.filter (fun j : ZMod n ↦ d[j] = 0)
local notation "horizontalNodes" =>
  Finset.univ.filter (fun j : ZMod n ↦ 0 < d[j] ∧ 0 < d[j + 1])

variable (hK : LineBundleClass.mk hD.toInvertibleSheaf =
  LineBundleClass.mk (QPainleve.canonicalBundle ℂ Φ.algebraicRealization 2))

include hc A hD hK in
private theorem sum_numbered_fiber_degrees : ∑ j : ZMod n, d[j] = 2 := by
  have hn : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ S) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsReduced D.subscheme := hn.isReduced
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  calc
    ∑ j : ZMod n, d[j] =
        ∑ q : D.boundaryPrimes, deg (D.boundaryPrimeEmbedding q) :=
      Equiv.sum_comp (A.boundaryPrimeEquiv hD) (fun q ↦ deg (D.boundaryPrimeEmbedding q))
    _ = 2 := Φ.sum_hirzebruch_boundary_prime_coordinates b e hΦ hc r hr hD hK 1

include hc A hD hK in
private theorem fiber_degree_pos_or_pos_at_node (j : ZMod n) : 0 < d[j] ∨ 0 < d[j + 1] := by
  by_contra! h
  have hdeg (k : ZMod n) := Φ.hirzebruch_fiber_degree_nonneg b e hΦ r hr hc (prime[k])
  have hz : d[j] = 0 := le_antisymm h.1 (hdeg j)
  have hz' : d[j + 1] = 0 := le_antisymm h.2 (hdeg (j + 1))
  by_cases hne : j ≠ j + 1
  · have hdis := Φ.disjoint_of_hirzebruch_fiber_degree_eq_zero b e hΦ hc r hr
      (D.boundaryPrimeEmbedding.injective.ne ((A.boundaryPrimeEquiv hD).injective.ne hne)) hz hz'
    have hleft := (A.ambientNode_mem_closure_boundaryPrime_iff hD j j).mpr ⟨0, by simp⟩
    have hright := (A.ambientNode_mem_closure_boundaryPrime_iff hD j (j + 1)).mpr ⟨1, by simp⟩
    exact Set.disjoint_left.mp hdis (by simpa only [D.coe_boundaryPrimeEmbedding] using hleft)
      (by simpa only [D.coe_boundaryPrimeEmbedding] using hright)
  · have h1 : (1 : ZMod n) = 0 := by simpa only [add_eq_left] using (not_ne_iff.mp hne).symm
    let : Subsingleton (ZMod n) := subsingleton_of_zero_eq_one h1.symm
    have hsum := sum_numbered_fiber_degrees b e hΦ hc r hr A hD hK
    have hsingle := Finset.sum_eq_single (f := fun k ↦ d[k]) j
      (s := Finset.univ) (fun k _ hk ↦ (hk (Subsingleton.elim k j)).elim) (by simp)
    rw [hsingle, hz] at hsum
    omega

include hc A hD hK in
/-- The number of nodes with two horizontal branches plus twice the number of
degree-zero components is the length of a numbered nodal anticanonical cycle. -/
theorem card_hirzebruch_horizontal_nodes_add_twice_vertical :
    (horizontalNodes).card + 2 * (vertical).card = n := by
  have hshift :
      (∑ j : ZMod n, if d[j + 1] = 0 then (1 : ℕ) else 0) = (vertical).card := by
    calc
      _ = ∑ j : ZMod n, if d[j] = 0 then (1 : ℕ) else 0 :=
        Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) _
      _ = _ := by simp
  have hcount (j : ZMod n) :
      (if 0 < d[j] ∧ 0 < d[j + 1] then (1 : ℕ) else 0) +
        (if d[j] = 0 then 1 else 0) + (if d[j + 1] = 0 then 1 else 0) = 1 := by
    have ha := Φ.hirzebruch_fiber_degree_nonneg b e hΦ r hr hc (prime[j])
    have hb := Φ.hirzebruch_fiber_degree_nonneg b e hΦ r hr hc (prime[j + 1])
    have hor := fiber_degree_pos_or_pos_at_node b e hΦ hc r hr A hD hK j
    split_ifs <;> omega
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ ↦ hcount j)
  simp [Finset.sum_add_distrib, hshift, ZMod.card] at hsum
  omega

include hc A hD hK in
private theorem exists_horizontal_node_or_terminal_degrees
    (hOver : D.subscheme ↘ S = D.subschemeι ≫ X ↘ S) :
    (∃ j : ZMod n, D.IsNodeOfReducedBoundary (X ↘ S) (A.ambientNode j) ∧
      ∀ k : ZMod n, A.ambientNode j ∈ closure {(A.boundaryPrimeEquiv hD k).val} → 0 < d[k]) ∨
    n = 4 ∨ (n = 2 ∧ ∃ j : ZMod n, d[j] = 2) := by
  have hcount := card_hirzebruch_horizontal_nodes_add_twice_vertical b e hΦ hc r hr A hD hK
  by_cases h : (horizontalNodes).Nonempty
  · obtain ⟨j, hj⟩ := h
    have hpos := (Finset.mem_filter.mp hj).2
    refine Or.inl ⟨j, A.isNodeOfReducedBoundary_ambientNode j hOver, fun k hk ↦ ?_⟩
    obtain ⟨l, hl⟩ := (A.ambientNode_mem_closure_boundaryPrime_iff hD j k).mp hk
    fin_cases l
    · have hk' : j = k := by simpa using hl
      exact hk' ▸ hpos.1
    · have hk' : j + 1 = k := by simpa using hl
      exact hk' ▸ hpos.2
  · have hv := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    rw [hv, zero_add] at hcount
    have hd := sum_numbered_fiber_degrees b e hΦ hc r hr A hD hK
    let positive := Finset.univ.filter (fun j : ZMod n ↦ ¬ d[j] = 0)
    have hbound : (positive.card : ℤ) ≤ 2 := by
      rw [← hd]
      calc
        (positive.card : ℤ) = ∑ j : ZMod n, if ¬ d[j] = 0 then (1 : ℤ) else 0 :=
          (Finset.sum_boole _ _).symm
        _ ≤ _ := Finset.sum_le_sum fun j _ ↦ by
          have hj := Φ.hirzebruch_fiber_degree_nonneg b e hΦ r hr hc (prime[j])
          split_ifs <;> omega
    have hparts : (vertical).card + positive.card = n := by
      simpa only [positive, Finset.card_univ, ZMod.card] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j : ZMod n ↦ d[j] = 0)
    have hn : n ≠ 0 := NeZero.ne n
    have hcases : n = 4 ∨ n = 2 := by omega
    rcases hcases with h₄ | h₂
    · exact Or.inr (Or.inl h₄)
    · have hcard : positive.card = 1 := by omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
      have hsum : ∑ k ∈ positive, d[k] = 2 := by
        rw [Finset.sum_filter, ← hd]
        exact Finset.sum_congr rfl fun k _ ↦ by split_ifs with hk <;> simp_all
      rw [hj, Finset.sum_singleton] at hsum
      exact Or.inr (Or.inr ⟨h₂, j, hsum⟩)

include hc A hD in
private theorem exists_ruling_fiber_omitted_of_node_degrees (j : ZMod n)
    (hpos : ∀ k : ZMod n, A.ambientNode j ∈ closure {(A.boundaryPrimeEquiv hD k).val} →
      0 < d[k]) :
    ∃ y : S ⟶ projectiveLine ℂ, y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧
      A.ambientNode j ∈ (y.ker.comap ruling).support ∧
      ¬ (y.ker.comap ruling).support ≤ D.support := by
  let x : X := A.ambientNode j
  let t := pointOfClosedPoint (X ↘ S) x (A.isClosed_ambientNode j)
  let y := t ≫ ruling
  have hy : y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S := by
    simpa only [y, Category.assoc, comp_over ruling S] using
      pointOfClosedPoint_comp (X ↘ S) x (A.isClosed_ambientNode j)
  have hx : x ∈ (y.ker.comap ruling).support := by
    rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, y.support_ker]
    apply subset_closure
    refine ⟨IsLocalRing.closedPoint ℂ, (Scheme.Hom.comp_apply _ _ _).trans ?_⟩
    exact congrArg ruling (pointOfClosedPoint_apply _ _ _ _)
  refine ⟨y, hy, hx, fun hle ↦ ?_⟩
  have hm : m ≠ 0 := by
    intro h
    simpa [Basis.coord_apply] using DFunLike.congr_fun h (b 1)
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hCartier := Φ.isEffectiveCartier_characterRuling_fiber m hR hm y hy
  obtain ⟨p', hp', hspec⟩ := hCartier.mem_support_iff_exists_codimensionOnePoint.mp hx
  let u : D.boundaryPrimes := ⟨p', mem_boundaryPrimes.mpr ⟨hle hp', p'.property⟩⟩
  obtain ⟨k, hk⟩ := (A.boundaryPrimeEquiv hD).surjective u
  have hp : prime[k] = p' := by
    rw [hk]
    exact Subtype.ext (D.coe_boundaryPrimeEmbedding u)
  have hmem : x ∈ closure {(A.boundaryPrimeEquiv hD k).val} := by
    rw [hk]
    exact specializes_iff_mem_closure.mp hspec
  exact (hpos k hmem).ne' (hp.symm ▸
    Φ.hirzebruch_fiber_degree_eq_zero_of_mem_ruling_fiber b e hΦ hc r hr hy hp')

include hc A hD hK in
/-- In a numbered nodal anticanonical cycle on a Hirzebruch surface, either a
numbered node lies on a rational ruling fiber omitted by the boundary, the
boundary has complexity zero, or it has two components and one is a bisection.
The first case supplies the center and the fiber for an elementary transformation. -/
theorem exists_hirzebruch_horizontal_node_or_boundary_cases
    (hOver : D.subscheme ↘ S = D.subschemeι ≫ X ↘ S) :
    (∃ (j : ZMod n) (y : S ⟶ projectiveLine ℂ),
      IsClosed ({A.ambientNode j} : Set X) ∧
      D.IsNodeOfReducedBoundary (X ↘ S) (A.ambientNode j) ∧
      y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S ∧ A.ambientNode j ∈ (y.ker.comap ruling).support ∧
      ¬ (y.ker.comap ruling).support ≤ D.support) ∨
    D.boundaryComplexity = 0 ∨ (n = 2 ∧ ∃ j : ZMod n, d[j] = 2) := by
  rcases exists_horizontal_node_or_terminal_degrees b e hΦ hc r hr A hD hK hOver with
    ⟨j, hj, hdeg⟩ | h₄ | h₂
  · obtain ⟨y, hy, hx, hf⟩ := exists_ruling_fiber_omitted_of_node_degrees b e hΦ hc r hr A hD j hdeg
    exact Or.inl ⟨j, y, A.isClosed_ambientNode j, hj, hy, hx, hf⟩
  · have hcard : D.boundaryPrimes.ncard = n := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_congr (A.boundaryPrimeEquiv hD), Nat.card_zmod]
    refine Or.inr (Or.inl ?_)
    rw [boundaryComplexity_def, finrank_eq_card_basis C, Fintype.card_fin, hcard, h₄]
    norm_num
  · exact Or.inr (Or.inr h₂)

end TauCeti.Toric.Fan
