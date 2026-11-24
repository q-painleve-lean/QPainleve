/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.CurveIntersection
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import QPainleve.Geometry.Toric.Fan.Ruling.Torus
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Picard coordinates and fiber degrees of the toric quadric

The ruling exchange of the Hirzebruch fan of index zero interchanges the two
integral Picard coordinates. Transport of a closed point blowup tower by this exchange
preserves its ordered exceptional coefficients. The Picard coordinates also give the degree
on a nonzero fiber of the exchanged ruling, which bounds the orders of first centers on it.
-/

public noncomputable section

open AlgebraicGeometry Module
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "E" => quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))

include hr in
/-- Reindexing the quadric rays with the exchanged lattice basis exchanges the
two vectors of the Hirzebruch Picard basis. -/
theorem hirzebruchPicardBasis_quadric_swap [Nonempty Φ.cones] :
    let p := Equiv.swap (0 : Fin 2) 1
    let s := ((Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap 2 3)).trans r
    hirzebruchPicardBasis (b.reindex p) 0 hΦ s (quadric_swapped_generators b r hr) =
      (hirzebruchPicardBasis b 0 hΦ r hr).reindex p := by
  intro p s
  have hp₀ : p.symm 0 = 1 := rfl
  have hp₁ : p.symm 1 = 0 := rfl
  apply DFunLike.ext
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · rw [hirzebruchPicardBasis_apply_zero (b.reindex p) 0 hΦ s _,
      Basis.reindex_apply, hp₀, hirzebruchPicardBasis_apply_one]
    rfl
  · rw [hirzebruchPicardBasis_apply_one (b.reindex p) 0 hΦ s _,
      Basis.reindex_apply, hp₁, hirzebruchPicardBasis_apply_zero]
    rfl

include hr in
/-- Reframe a quadric so that the specified invariant fiber and its opposite become
the section rays. The two Picard basis vectors exchange places. -/
theorem exists_quadric_picardBasis_of_fiber [Nonempty Φ.cones] (t : Fin 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1]),
      s 0 = r ((![1, 3] : Fin 2 → Fin 4) t) ∧
      s 2 = r ((![1, 3] : Fin 2 → Fin 4) (Equiv.swap 0 1 t)) ∧
      hirzebruchPicardBasis d 0 hΦ s hs =
        (hirzebruchPicardBasis b 0 hΦ r hr).reindex (Equiv.swap 0 1) := by
  obtain ⟨a, u, hu, -, h₁, hpic⟩ := exists_hirzebruch_picardBasis_of_fiber b 0 r hr hΦ t
  have hop (j : Fin 2) :
      (r ((![1, 3] : Fin 2 → Fin 4) (Equiv.swap 0 1 j))).primitiveGenerator =
        -(r ((![1, 3] : Fin 2 → Fin 4) j)).primitiveGenerator := by
    fin_cases j <;> simp [congrFun hr]
  have h₃ : u 3 = r ((![1, 3] : Fin 2 → Fin 4) (Equiv.swap 0 1 t)) := by
    apply Ray.primitiveGenerator_injective
    rw [hop, ← h₁, congrFun hu 3, congrFun hu 1]
    simp
  refine ⟨a.reindex (Equiv.swap 0 1), ((Equiv.swap 0 1).trans (Equiv.swap 2 3)).trans u,
    quadric_swapped_generators a u hu, h₁, h₃, ?_⟩
  rw [hirzebruchPicardBasis_quadric_swap a hΦ u hu, hpic]

include hc hr in
open PointedCone in
/-- At a corner on the opposite invariant fiber (ray `r 3`), choose a quadric marking
whose generators span the corner cone and whose opposite section is the original
fiber ray `r 1`. The two Picard basis vectors exchange places. -/
theorem exists_exchanged_marking_at_opposite_corner [Nonempty Φ.cones]
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (hopp : (r 3).toCone ≤ σ) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1]),
      σ.val = hull ℝ (Set.range (i ∘ d)) ∧ s 2 = r 1 ∧
      Φ.hirzebruchPicardBasis d 0 hΦ s hs =
        (Φ.hirzebruchPicardBasis b 0 hΦ r hr).reindex (Equiv.swap 0 1) := by
  obtain ⟨a, u, hu, hu₀, hu₂, hpic⟩ := Φ.exists_quadric_picardBasis_of_fiber b hΦ r hr 1
  have ha : (u 0).toCone ≤ σ := hu₀.symm ▸ hopp
  obtain ⟨d, e, s, hcone, he, hfib, hsec⟩ :=
    Φ.exists_hirzebruch_corner_basis a 0 u hu hΦ hc σ hσ
  have hgen₀ : (s 0).primitiveGenerator = d 0 := congrFun he 0
  have hmem : i ((s 0).primitiveGenerator) ∈ σ.val := by
    rw [hgen₀, hcone]
    exact subset_hull ⟨0, rfl⟩
  have hs₀ : s 0 = u 0 ∧ e = 0 := by
    rcases hsec with h | ⟨h, he'⟩
    · exact h
    · have hpos : i (a 0) ∈ σ.val := ha (by
        rw [Fan.Ray.toCone_eq_hull_primitiveGenerator]
        exact subset_hull (by simp [congrFun hu 0]))
      have hneg : -(i (a 0)) ∈ σ.val := by
        have hu₂' : (u 2).primitiveGenerator = -a 0 := congrFun hu 2
        simpa only [h, hu₂', map_neg] using hmem
      have hn : i (a 0) ≠ 0 :=
        fun hz ↦ (a.ne_zero 0) (Φ.lattice.injective (hz.trans (map_zero i).symm))
      exact ((Φ.isToricCone σ.property).salient _ hpos hn hneg).elim
  obtain ⟨hs₀, rfl⟩ := hs₀
  refine ⟨d, s, he, hcone, ?_, ?_⟩
  · have h : d 0 = a 0 :=
      hgen₀.symm.trans ((congrArg Fan.Ray.primitiveGenerator hs₀).trans (congrFun hu 0))
    exact hu₂ ▸ Fan.Ray.primitiveGenerator_injective
      ((congrFun he 2).trans ((congrArg Neg.neg h).trans (congrFun hu 2).symm))
  · rw [← hpic]
    apply DFunLike.ext
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · rw [Fan.hirzebruchPicardBasis_apply_zero]
      rcases hfib with h | h
      · rw [h, ← Fan.hirzebruchPicardBasis_apply_zero a 0 hΦ u hu]
      · rw [h, ← Fan.hirzebruchPicardBasis_apply_zero_eq_ray_three a 0 hΦ u hu]
    · rw [Fan.hirzebruchPicardBasis_apply_one, hs₀,
        ← Fan.hirzebruchPicardBasis_apply_one a 0 hΦ u hu]

variable [Nonempty Φ.cones]

local notation "C" => hirzebruchPicardBasis b 0 hΦ r hr

open LineBundleClass in
/-- Pullback along the ruling exchange swaps the two Hirzebruch Picard coordinates. -/
theorem hirzebruchPicardBasis_repr_pullback_quadricRulingExchange
    (L : Additive (LineBundleClass Φ.algebraicRealization)) (j : Fin 2) :
    (C).repr (Additive.ofMul (pullback τ L.toMul)) j = (C).repr L (Equiv.swap 0 1 j) := by
  let P := (pullbackHom τ).toAdditive.toIntLinearMap
  have hP (k : Fin 2) : P (C k) = C (Equiv.swap 0 1 k) := by
    have h₀ := (E).pullback_primeDivisorClass_rayBoundaryPoint hΦ hΦ (r 0)
    have h₁ := (E).pullback_primeDivisorClass_rayBoundaryPoint hΦ hΦ (r 1)
    simp only [quadricRulingExchange_rayEquiv, sub_zero, sub_self] at h₀ h₁
    fin_cases k
    · simpa [P, rayDivisorToPicard_single] using congrArg Additive.ofMul h₀
    · simpa [P, rayDivisorToPicard_single] using congrArg Additive.ofMul h₁
  have he : P = (C).equiv (C) (Equiv.swap 0 1) := by
    apply (C).ext
    intro k
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hP]
  have hPL : P L = Additive.ofMul (pullback τ L.toMul) := by simp [P]
  rw [← hPL, he, LinearEquiv.coe_coe, Basis.equiv, LinearEquiv.trans_apply]
  let s := Equiv.swap (0 : Fin 2) 1
  have h := (C).repr_reindex_apply (e := s.symm)
    (((C).reindex s.symm).repr.symm ((C).repr L)) (s j)
  simpa only [s, Equiv.symm_symm, Equiv.swap_apply_self, LinearEquiv.apply_symm_apply] using h.symm

end TauCeti.Toric.Fan

namespace QPainleve.BlowupTower.IsClosedPointTower

open CategoryTheory TauCeti.Toric LineBundleClass

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "Pic" => Additive (LineBundleClass X)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "E" => Fan.quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))
local notation "Q(" T ")" => BlowupTower.transport T (asIso τ)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

/-- On transport of a closed point tower by the toric ruling exchange, the base
coordinates of a line bundle are transposed and its total exceptional coefficients
are unchanged. The transported line bundle is pulled back along the inverse lift. -/
theorem picardMarking_symm_rulingExchange (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let q := Q(T)
    let hQ := q.isLift.isClosedPointTower hT
    let v : Pic × (Fin n → ℤ) := (T.picardMarking hT f).symm (Additive.ofMul L)
    let w : Pic × (Fin n → ℤ) :=
      (q.tower.picardMarking hQ f).symm (Additive.ofMul (pullback q.iso.inv L))
    (∀ j : Fin 2, (C).repr w.1 j = (C).repr v.1 (Equiv.swap 0 1 j)) ∧ w.2 = v.2 := by
  intro hSmooth q hQ v w
  let : SmoothOfRelativeDimension 2 f := hSmooth
  have hτ : (asIso τ).inv = τ := by
    apply (cancel_mono τ).mp
    exact (by simpa only [asIso_hom] using (asIso τ).inv_hom_id :
      (asIso τ).inv ≫ τ = 𝟙 X).trans (Fan.quadricRulingExchange_algebraicMap_comp ..).symm
  have hv : (T.picardHom v).toMul = L := by
    rw [← picardMarking_apply T hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hw : w = (Additive.ofMul (pullback τ v.1.toMul), v.2) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [toMul_ofMul, picardMarking_apply]
    simpa only [Iso.symm_hom, hτ, hv, Prod.mk.eta] using q.isLift.symm.pullback_picardHom v.1 v.2
  rw [hw]
  exact ⟨Fan.hirzebruchPicardBasis_repr_pullback_quadricRulingExchange b hΦ hc r hr v.1, rfl⟩

local notation "Plane" => Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Fin 3 → ℂ))

omit [Nonempty Φ.cones] in
/-- Every base order of a resolved plane line system on a toric quadric is bounded
by its fiber degree in the exchanged ruling. This degree is the first Hirzebruch
Picard coordinate in the given frame. -/
theorem base_order_le_quadric_exchanged_fiber_degree [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (g : Y ⟶ Plane) (hg : g ≫ (Plane ↘ S) = T.toBase ≫ f) (j : Fin n) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let H := mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (-v.2 j) ≤ (C).repr v.1 0 := by
  intro hcones hSmooth H v
  let := hcones
  let := hSmooth
  let q := Q(T)
  let hQ := q.isLift.isClosedPointTower hT
  have hg' : (q.iso.inv ≫ g) ≫ (Plane ↘ S) = q.tower.toBase ≫ f := by
    apply (cancel_epi q.iso.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id_assoc, hg, ← Category.assoc, q.isLift.hom_toBase,
      Category.assoc, asIso_hom, comp_over τ S]
  have hbound := hQ.base_order_le_hirzebruch_fiber_degree b 0 hΦ r hr hc (q.iso.inv ≫ g) hg' j
  have ⟨hBase, hOrders⟩ := hT.picardMarking_symm_rulingExchange b hΦ hc r hr (pullback g H)
  dsimp only at hbound hBase hOrders
  rw [← pullback_comp, hOrders, hBase, Equiv.swap_apply_right] at hbound
  exact hbound

section

open Limits Chow

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

local notation "P" => projectiveLine ℂ
local notation "d" => b.reindex (Equiv.swap 0 1)
local notation "m" => LinearMap.toAddMonoidHom (Basis.coord b 0)
local notation "p(" t ")" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (t : ℂ)

local notation "h" => Fan.nonneg_or_nonpos_quadric_transverse_character b r hr
local notation "ruling" => Φ.characterRuling m h

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
      Set.range j = ruling ⁻¹' Set.range (p(t)) ∧
      ∀ L : Additive (LineBundleClass X), intersectionNumber ℂ j L.toMul = (C).repr L 0 := by
  classical
  obtain ⟨hp, hn⟩ := Fan.quadric_transverse_ruling_rays b r hr
  have hcoord : m = ((d).coord 1).toAddMonoidHom := by
    ext x
    simp [Basis.coord_apply]
  let e := Φ.characterRulingNonzeroFiberIso m h d hcoord
    (by simpa using hp) (by simpa using hn) t
  let j := e.inv ≫ pullback.fst ruling (p(t))
  have ht : p(t) ≫ (P ↘ S) = 𝟙 S := by simp [projectiveLine.polynomialPoint_over]
  have : IsClosedImmersion (p(t)) := (p(t)).isClosedImmersion_of_comp_eq_id ht
  have hj : IsClosedImmersion j := inferInstance
  have he := Φ.characterRulingNonzeroFiberIso_hom_comp_over m h d hcoord
    (by simpa using hp) (by simpa using hn) t
  have hver : e.inv ≫ pullback.snd ruling (p(t)) = P ↘ S := by
    rw [← he, Iso.inv_hom_id_assoc]
  have hbase : j ≫ (X ↘ S) = P ↘ S := by
    dsimp only [j]
    rw [← comp_over ruling S, Category.assoc, pullback.condition_assoc,
      ← Category.assoc e.inv, hver, ht, Category.comp_id]
  refine ⟨j, hj, hbase, ?_, fun L ↦ ?_⟩
  · rw [range_eq_range_of_surjective j (pullback.fst ruling (p(t))) e.inv rfl,
      Scheme.Pullback.range_fst]
  have hm : m ≠ 0 := by
    intro hz
    have hd : m (b 0) = 1 := by simp
    rw [hz, AddMonoidHom.zero_apply] at hd
    norm_num at hd
  have hker : j.ker = (p(t)).ker.comap ruling := by
    dsimp only [j]
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback (p(t))
      (IsPullback.of_hasPullback ruling (p(t)))
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

include hc in
/-- The orders of selected first centers on a fiber of the exchanged quadric ruling
over a point of the base torus sum to at most the original degree on that fiber. -/
theorem sum_first_base_orders_le_quadric_transverse_fiber_degree
    (L : Additive (LineBundleClass X)) (orders : Fin n → ℕ) (s : Finset (Fin n)) (t : ℂˣ)
    (hs : ∀ j ∈ s, ruling (hT.baseCenter j) ∈ Set.range (p(t)) ∧
      ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hnef : (T.picardHom (L, fun l ↦ -(orders l : ℤ))).toMul.IsNef ℂ (T.toBase ≫ (X ↘ S))) :
    ∑ l ∈ s, (orders l : ℤ) ≤ (C).repr L 0 := by
  obtain ⟨j, hj, hjbase, hjrange, hjdeg⟩ := exists_quadric_transverse_fiber b hΦ hc r hr t
  have : Smooth (P ↘ S) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular P := IsRegular.of_smooth (P ↘ S)
  rw [← hjdeg L]
  exact hT.sum_first_base_orders_le_curve_intersection j (X ↘ S) hjbase.symm L.toMul orders s
    (fun l hl ↦ ⟨hjrange.symm ▸ (hs l hl).1, (hs l hl).2⟩) hnef

end

end QPainleve.BlowupTower.IsClosedPointTower
