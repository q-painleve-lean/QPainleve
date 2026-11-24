/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.CurveIntersection
public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.Geometry.Toric.Fan.Ruling.Torus
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Separation of high-multiplicity centers on the quadric

The two selected centers of the quadric link must lie on distinct fibers of the
exchanged ruling. The two-point Sarkisov inequality makes their combined order
larger than the degree on a transverse fiber. If they shared that fiber,
intersection with its strict transform on the specified resolution would
contradict nefness. This proves the separation in Case B of Proposition 8.11 in
Lutz's appendix to [*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => projectiveLine ℂ
local notation "X" => Φ.algebraicRealization
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "d" => b.reindex (Equiv.swap 0 1)
local notation "m" => LinearMap.toAddMonoidHom (Basis.coord b 0)
local notation "p(" t ")" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (t : ℂ)

local notation "h" => Fan.nonneg_or_nonpos_quadric_transverse_character b r hr
local notation "f" => Φ.characterRuling m h

omit [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ] in
include hr in
private theorem quadric_transverse_ruling_positive_part :
    (fun ρ : Φ.Ray ↦ max (m ρ.primitiveGenerator) 0) = Pi.single (r 0) 1 := by
  classical
  funext ρ
  obtain ⟨j, rfl⟩ := r.surjective ρ
  fin_cases j <;> simp [congrFun hr, Basis.coord_apply]

include hc in
private theorem quadric_intersection_section (L : Additive (LineBundleClass X)) :
    classIntersectionNumber ℂ X L.toMul (C 1).toMul = (C).repr L 0 := by
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let B := intersectionBilinForm ℂ X
  rw [← intersectionBilinForm_apply]
  calc
    B L (C 1) =
        B (((C).repr L 0) • C 0 + ((C).repr L 1) • C 1) (C 1) := by
      apply congrArg (fun L' ↦ B L' (C 1))
      simpa only [Fin.sum_univ_two] using ((C).sum_repr L).symm
    _ = _ := by
      simp only [B, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
        Int.zsmul_eq_mul, Fan.hirzebruchPicardBasis_intersection b 0 hΦ r hr hc]
      norm_num

include hc in
private theorem exists_quadric_transverse_fiber (t : ℂˣ) :
    ∃ j : P ⟶ X, IsClosedImmersion j ∧ j ≫ (X ↘ S) = P ↘ S ∧
      Set.range j = f ⁻¹' Set.range (p(t)) ∧
      ∀ L : Additive (LineBundleClass X), intersectionNumber ℂ j L.toMul = (C).repr L 0 := by
  classical
  obtain ⟨hp, hn⟩ := Fan.quadric_transverse_ruling_rays b r hr
  have hcoord : m = ((d).coord 1).toAddMonoidHom := by
    ext x
    simp [Basis.coord_apply]
  let e := Φ.characterRulingNonzeroFiberIso m h d hcoord
    (by simpa using hp) (by simpa using hn) t
  let j := e.inv ≫ pullback.fst f (p(t))
  have ht : p(t) ≫ (P ↘ S) = 𝟙 S := by simp [projectiveLine.polynomialPoint_over]
  have : IsClosedImmersion (p(t)) := (p(t)).isClosedImmersion_of_comp_eq_id ht
  have hj : IsClosedImmersion j := inferInstance
  have he := Φ.characterRulingNonzeroFiberIso_hom_comp_over m h d hcoord
    (by simpa using hp) (by simpa using hn) t
  have hver : e.inv ≫ pullback.snd f (p(t)) = P ↘ S := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hbase : j ≫ (X ↘ S) = P ↘ S := by
    dsimp only [j]
    rw [← comp_over f S, Category.assoc, pullback.condition_assoc,
      ← Category.assoc e.inv, hver, ht, Category.comp_id]
  refine ⟨j, hj, hbase, ?_, fun L ↦ ?_⟩
  · rw [range_eq_range_of_surjective j (pullback.fst f (p(t))) e.inv rfl,
      Scheme.Pullback.range_fst]
  have hm : m ≠ 0 := by
    intro hz
    have hd : m (b 0) = 1 := by simp
    rw [hz, AddMonoidHom.zero_apply] at hd
    norm_num at hd
  have hker : j.ker = (p(t)).ker.comap f := by
    dsimp only [j]
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback (p(t))
      (IsPullback.of_hasPullback f (p(t)))
  let hcart := Φ.isEffectiveCartier_characterRuling_fiber m h hm (p(t)) ht
  have hclass := Φ.toLineBundleClass_characterRuling_fiber m h hm (p(t)) ht hΦ
  simp only [Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
    quadric_transverse_ruling_positive_part b r hr] at hclass
  rw [← Fan.hirzebruchPicardBasis_apply_one b 0 hΦ r hr] at hclass
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have : SmoothOfRelativeDimension 2 (X ↘ S) :=
    hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : j.IsOver S := ⟨hbase⟩
  have hjcart : j.ker.IsEffectiveCartier := hker.symm ▸ hcart
  rw [← classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker ℂ
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)).le j
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ) hjcart L.toMul]
  have heq := mk_toInvertibleSheaf_congr hjcart hcart hker
  have hpic := congrArg Additive.toMul hclass
  rw [toMul_ofMul] at hpic
  rw [heq, hpic, quadric_intersection_section b hΦ hc r hr L]

variable {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

include hc in
/-- The orders of selected first centers on a fiber of the exchanged quadric ruling
over a point of the base torus sum to at most the original degree on that fiber. -/
theorem sum_first_base_orders_le_quadric_transverse_fiber_degree
    (L : Additive (LineBundleClass X)) (orders : Fin n → ℕ) (s : Finset (Fin n)) (t : ℂˣ)
    (hs : ∀ j ∈ s, f (hT.baseCenter j) ∈ Set.range (p(t)) ∧
      ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hnef : (T.picardHom (L, fun l ↦ -(orders l : ℤ))).toMul.IsNef ℂ (T.toBase ≫ (X ↘ S))) :
    ∑ l ∈ s, (orders l : ℤ) ≤ (C).repr L 0 := by
  obtain ⟨j, hj, hjbase, hjrange, hjdeg⟩ := exists_quadric_transverse_fiber b hΦ hc r hr t
  have : Smooth (P ↘ S) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular P := IsRegular.of_smooth (P ↘ S)
  rw [← hjdeg L]
  exact hT.sum_first_base_orders_le_curve_intersection j (X ↘ S) hjbase.symm L.toMul orders s
    (fun l hl ↦ ⟨hjrange.symm ▸ (hs l hl).1, (hs l hl).2⟩) hnef

include hc in
private theorem ne_quadric_transverse_ruling_of_homaloidal
    (L : Additive (LineBundleClass X)) (orders : Fin n → ℕ) {j l : Fin n} (hjl : j ≠ l)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j)
    (hl : ∀ i < l, hT.baseCenter i ≠ hT.baseCenter l)
    (t : ℂˣ) (ht : f (hT.baseCenter j) ∈ Set.range (p(t)))
    (hnef : (T.picardHom (L, fun i ↦ -(orders i : ℤ))).toMul.IsNef ℂ (T.toBase ≫ (X ↘ S))) :
    let a := (C).repr L 0
    let β := (C).repr L 1
    (∑ i, (orders i : ℤ) ^ 2) = 2 * a * β - 1 →
    (∑ i, (orders i : ℤ)) = 2 * a + 2 * β - 3 →
    β < 2 * (orders j : ℤ) → (orders j : ℤ) ≤ β →
    β < 2 * (orders l : ℤ) → (orders l : ℤ) ≤ β →
    (∀ i, i ≠ j → i ≠ l → 2 * (orders i : ℤ) ≤ β) →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro a β hsq hsum hjbig hjle hlbig hlle hsmall heq
  classical
  have hβ : 0 < β := by omega
  have hnum := quadric_sarkisov_degree_decrease_of_pair hβ hjl hsq hsum hjbig.le hjle hlbig.le hlle
    (fun i hi hi' ↦ ⟨Nat.cast_nonneg _, hsmall i hi hi'⟩)
  have hbound := hT.sum_first_base_orders_le_quadric_transverse_fiber_degree
    b hΦ hc r hr L orders {j, l} t (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨ht, hj⟩
      · exact ⟨heq ▸ ht, hl⟩) hnef
  rw [Finset.sum_pair hjl] at hbound
  omega

local notation "P₂" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "π" => T.toBase ≫ (X ↘ S)

include hc in
/-- For a resolved quadric-to-plane map in the two-high-order case, the selected
proper centers lie on distinct fibers of the exchanged ruling if one lies over the
base torus. The orders are read from the total exceptional coordinates of the
resolved line class. Each selected order is at most the original fiber degree, and
every other order is at most half that degree. -/
theorem ne_quadric_transverse_ruling_of_two_high_base_orders
    (g : Y ⟶ P₂) (hg : g ≫ (P₂ ↘ S) = π) (hbir : Scheme.BirationalOver g (𝟙 P₂))
    {j l : Fin n} (hjl : j ≠ l)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j)
    (hl : ∀ i < l, hT.baseCenter i ≠ hT.baseCenter l)
    (t : ℂˣ) (ht : f (hT.baseCenter j) ∈ Set.range (p(t))) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let v := (T.picardMarking hT (X ↘ S)).symm (Additive.ofMul (pullback g H))
    let β := (C).repr v.1 1
    (∀ i, 0 ≤ -v.2 i) →
    β < 2 * (-v.2 j) → -v.2 j ≤ β →
    β < 2 * (-v.2 l) → -v.2 l ≤ β →
    (∀ i, i ≠ j → i ≠ l → 2 * (-v.2 i) ≤ β) →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro hSmooth v β hn hjbig hjle hlbig hlle hsmall
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hSmooth
  let orders (i : Fin n) := (-v.2 i).toNat
  have horders (i : Fin n) : (orders i : ℤ) = -v.2 i := Int.toNat_of_nonneg (hn i)
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hmark := congrArg Additive.toMul ((T.picardMarking hT (X ↘ S)).apply_symm_apply
    (Additive.ofMul (pullback g H)))
  rw [T.picardMarking_apply, toMul_ofMul] at hmark
  have hneg : (fun i ↦ -(orders i : ℤ)) = v.2 := funext fun i ↦ by rw [horders, neg_neg]
  have hample : (H).IsAmple :=
    TauCeti.SymmetricAlgebra.isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  let : Y.Over S := ⟨π⟩
  have : g.IsOver S := ⟨hg⟩
  have hnef : (T.picardHom (v.1, fun i ↦ -(orders i : ℤ))).toMul.IsNef ℂ π := by
    rw [hneg, Prod.mk.eta, hmark]
    exact hample.isNef.pullback g
  refine ne_quadric_transverse_ruling_of_homaloidal b hΦ hc r hr hT v.1 orders hjl hj hl t ht hnef
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [horders, neg_sq, Nat.cast_zero, zero_mul, sub_zero] using hsq
  · simpa only [horders, Nat.cast_zero, sub_zero] using hsum
  · simpa only [horders] using hjbig
  · simpa only [horders] using hjle
  · simpa only [horders] using hlbig
  · simpa only [horders] using hlle
  · simpa only [horders] using hsmall

end QPainleve.BlowupTower.IsClosedPointTower
