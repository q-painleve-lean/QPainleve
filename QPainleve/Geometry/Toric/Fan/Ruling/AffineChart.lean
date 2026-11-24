/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch

import Mathlib.LinearAlgebra.Transvection.Basic
import QPainleve.Geometry.Toric.Fan.Equiv
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Scheme
import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism
import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# Affine charts of a Hirzebruch ruling

Over either polynomial chart of the projective line, the character ruling of a
Hirzebruch fan is a projective-line product. The two product coordinates come
from a lattice basis adapted to the selected fiber ray. These trivializations
give the local models for the projective bundle description of the ruling.

The construction uses the product of toric fans and the inverse image of an
open subfan. See Fulton, *Introduction to Toric Varieties*, §1.4 and §2.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module Multiplicative PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "L" => projectiveLine ℂ
local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "C[" k "]" =>
  Fan.projectiveSpaceMaximalCone (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
    (finSuccEquiv 1 k)

private abbrev chartFaces (k : Fin 2) : Set (PointedCone ℝ (Fin 1 → ℝ)) :=
  {σ | σ.IsFaceOf (C[k]).val}

local notation "F[" k "]" => chartFaces k

private theorem chart_faces_subset (k : Fin 2) : F[k] ⊆ (P).cones :=
  (P).isFaceOf_subset_cones (C[k]).property

private theorem chart_faces_closed (k : Fin 2) ⦃σ τ⦄
    (hσ : σ ∈ F[k]) (hτ : τ.IsFaceOf σ) : τ ∈ F[k] :=
  hτ.trans hσ

local notation "A[" k "]" => Fan.subfan P F[k] (chart_faces_subset k) (chart_faces_closed k)
local notation "ι[" k "]" =>
  Fan.subfanInclusion P F[k] (chart_faces_subset k) (chart_faces_closed k)

private theorem chart_support (k : Fin 2) : (A[k]).support = (C[k]).val := by
  rw [← (P).ofCone_eq_subfan (C[k]).property, Fan.support_ofCone]

private def chartIso (k : Fin 2) : (A[k]).algebraicRealization ≅ Spec (.of (Polynomial ℂ)) := by
  let σ : (A[k]).cones := ⟨(C[k]).val, by rw [Fan.subfan_cones]; exact .refl _⟩
  let j := (A[k]).affineToricChartι σ
  let : IsIso j := (A[k]).isIso_affineToricChartι_of_forall_le fun τ ↦ by
    obtain ⟨τ, hτ⟩ := τ
    rw [Fan.subfan_cones] at hτ
    exact PointedCone.IsFaceOf.le hτ
  let f := j ≫ (ι[k]).algebraicMap ≫ projectiveLineToricIso.hom
  let : IsOpenImmersion (ι[k]).algebraicMap :=
    (P).isOpenImmersion_subfanInclusion_algebraicMap _ _ _
  have hf : f = (P).affineToricChartι C[k] ≫ projectiveLineToricIso.hom := by
    dsimp only [f, j]
    rw [affineToricChartι_comp_subfanInclusion_algebraicMap_assoc]
  exact (asIso j).symm ≪≫ IsOpenImmersion.isoOfRangeEq f (projectiveLine.polynomialChartι ℂ k)
    (hf ▸ range_affineToricChartι_comp_projectiveLineToricIso k)

@[reassoc]
private theorem chartIso_hom_comp_polynomialChartι (k : Fin 2) :
    (chartIso k).hom ≫ projectiveLine.polynomialChartι ℂ k =
      (ι[k]).algebraicMap ≫ projectiveLineToricIso.hom := by
  simp [chartIso, IsOpenImmersion.isoOfRangeEq_hom_fac]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom) (k : Fin 2)

local notation "charMap" => Φ.characterFanHom m h
local notation "U" => FanHom.preimageSubfan charMap F[k] (chart_faces_closed k)
local notation "g" =>
  FanHom.restrictToPreimage charMap F[k] (chart_faces_subset k) (chart_faces_closed k)
local notation "Q" => Fan.prod P A[k]
local notation "W" => (Fin 1 → ℝ)

local notation "coordZ" =>
  LinearEquiv.toAddEquiv (LinearEquiv.trans (Basis.equivFun b)
    (LinearEquiv.trans (LinearEquiv.finTwoArrow ℤ ℤ)
      (LinearEquiv.prodCongr (LinearEquiv.symm (LinearEquiv.funUnique (Fin 1) ℤ ℤ))
        (LinearEquiv.symm (LinearEquiv.funUnique (Fin 1) ℤ ℤ)))))
local notation "E" => IsIntegralLattice.extendEquiv (Fan.lattice U) (Fan.lattice Q) coordZ
local notation "M" => PointedCone.map (LinearEquiv.toLinearMap E)

private theorem chartCoordinates_apply (x : N) :
    coordZ x = (fun _ ↦ b.coord 0 x, fun _ ↦ b.coord 1 x) := (rfl)

include hm in
private theorem characterFanHom_realMap_eq_chartCoordinates_snd (x : V) :
    (charMap).realMap x = (E x).2 := by
  have he : (charMap).realMap = (LinearMap.snd ℝ W W).comp (E).toLinearMap := by
    apply Φ.lattice.isBaseChange.algHom_ext
    intro n
    simp only [AddMonoidHom.coe_toIntLinearMap]
    rw [(charMap).map_lattice]
    have hl : (charMap).latticeMap n = fun _ ↦ b.coord 1 n := by
      funext j
      rw [characterFanHom_latticeMap]
      exact DFunLike.congr_fun hm n
    rw [hl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      (U).lattice.extendEquiv_apply_lattice, LinearMap.snd_apply, chartCoordinates_apply]
    rfl
  exact DFunLike.congr_fun he x

include hm in
private theorem mem_chart_preimage_iff {σ : PointedCone ℝ V} :
    σ ∈ (U).cones ↔ σ ∈ Φ.cones ∧ (∀ x ∈ σ, (E x).2 ∈ (C[k]).val) := by
  rw [Fan.subfan_cones]
  constructor
  · intro hpre
    have hσ := (charMap).preimageCones_subset F[k] hpre
    have hface := ((charMap).mem_preimageCones_iff F[k] hσ).mp hpre
    refine ⟨hσ, fun x hx ↦ (PointedCone.IsFaceOf.le hface) ?_⟩
    rw [← characterFanHom_realMap_eq_chartCoordinates_snd Φ m h b hm k x]
    exact (charMap).map_le_leastCone hσ ⟨x, hx, rfl⟩
  · rintro ⟨hσ, hmap⟩
    refine ((charMap).mem_preimageCones_iff F[k] hσ).mpr
      ((P).isFaceOf_of_le (C[k]).property ((charMap).leastCone_mem hσ) ?_)
    apply (charMap).leastCone_le hσ (C[k]).property
    rintro _ ⟨x, hx, rfl⟩
    exact (characterFanHom_realMap_eq_chartCoordinates_snd Φ m h b hm k x).symm ▸ hmap x hx

private theorem map_chart_corner (j : Fin 2) :
    M (hull ℝ {i (if j = 0 then b 0 else -b 0), i (if k = 0 then b 1 else -b 1)}) =
      (C[j]).val.prod (C[k]).val := by
  have hp (v : N) : E (i v) = (AddMonoidHom.prodMap
      ((Int.castAddHom ℝ).compLeft (Fin 1)) ((Int.castAddHom ℝ).compLeft (Fin 1))) (coordZ v) :=
    (U).lattice.extendEquiv_apply_lattice (Q).lattice coordZ v
  have h₀ : E (i (b 0)) = ((1 : W), 0) := by
    rw [hp, chartCoordinates_apply]
    ext l <;> simp [Basis.coord_apply]
  have h₁ : E (i (b 1)) = (0, (1 : W)) := by
    rw [hp, chartCoordinates_apply]
    ext l <;> simp [Basis.coord_apply]
  have he₀ : E (i (if j = 0 then b 0 else -b 0)) = ((if j = 0 then 1 else -1 : W), 0) := by
    split_ifs <;> simp [h₀]
  have he₁ : E (i (if k = 0 then b 1 else -b 1)) = (0, (if k = 0 then 1 else -1 : W)) := by
    split_ifs <;> simp [h₁]
  have hs (l : Fin 2) : (C[l]).val = hull ℝ {(if l = 0 then 1 else -1 : W)} := by
    rw [projectiveSpaceMaximalCone_finOne_val]
    split_ifs <;> first | exact affineRayCone_def | exact negativeRayCone_def
  rw [PointedCone.map, Submodule.map_span, Set.image_pair]
  -- The real extension as a linear map over the nonnegative scalars has the same values.
  rw [show (↑(E).toLinearMap : V →ₗ[Nonneg ℝ] (W × W))
        (i (if j = 0 then b 0 else -b 0)) = _ from he₀,
      show (↑(E).toLinearMap : V →ₗ[Nonneg ℝ] (W × W))
        (i (if k = 0 then b 1 else -b 1)) = _ from he₁,
      hs j, hs k, ← LinearMap.span_inl_union_inr, Set.image_singleton, Set.image_singleton,
      Set.singleton_union]
  rfl

include hm in
private theorem chart_product_cones_subset
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) :
    (Q).cones ⊆ ((U).mapEquiv (Q).lattice coordZ).cones := by
  have hmax (j : Fin 2) : (C[j]).val.prod (C[k]).val ∈ ((U).mapEquiv (Q).lattice coordZ).cones := by
    rw [mapEquiv_cones, ← map_chart_corner Φ m h b k j]
    refine Set.mem_image_of_mem _ ((mem_chart_preimage_iff Φ m h b hm k).2
      ⟨hcorners j, fun x hx ↦ ?_⟩)
    have hmem : E x ∈ M (hull ℝ {i (if j = 0 then b 0 else -b 0),
        i (if k = 0 then b 1 else -b 1)}) := ⟨x, hx, rfl⟩
    rw [map_chart_corner Φ m h b k j] at hmem
    exact hmem.2
  intro σ hσ
  obtain ⟨a, ha, c, hc, rfl⟩ := (Fan.mem_prod_cones _ _).1 hσ
  have hc' : c.IsFaceOf (C[k]).val := by rwa [Fan.subfan_cones] at hc
  rw [projectiveSpace_finOne_eq_projectiveLineFan, mem_projectiveLineFan_cones] at ha
  have ha' : ∃ j : Fin 2, a.IsFaceOf (C[j]).val := by
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, ((P).isToricCone (C[0]).property).salient.bot_isFaceOf⟩
    · exact ⟨0, (projectiveSpaceMaximalCone_finOne_val 0).symm ▸ .refl _⟩
    · exact ⟨1, (projectiveSpaceMaximalCone_finOne_val 1).symm ▸ .refl _⟩
  obtain ⟨j, hj⟩ := ha'
  exact ((U).mapEquiv (Q).lattice coordZ).mem_of_isFaceOf (hmax j) (hj.prod hc')

include hm in
private def chartFanEquiv
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) : FanEquiv U Q where
  latticeEquiv := coordZ
  realEquiv := E
  map_lattice := (U).lattice.extendEquiv_apply_lattice (Q).lattice coordZ
  map_mem σ := by
    have hs : ((U).mapEquiv (Q).lattice coordZ).support ⊆ (Q).support := by
      have hP : (P).IsComplete := by
        rw [projectiveSpace_finOne_eq_projectiveLineFan]
        exact isComplete_projectiveLineFan
      rw [Fan.support_prod, chart_support]
      intro x hx
      obtain ⟨τ, hτ, hxτ⟩ := (((U).mapEquiv (Q).lattice coordZ).mem_support).1 hx
      rw [mapEquiv_cones] at hτ
      obtain ⟨ξ, hξ, rfl⟩ := hτ
      obtain ⟨y, hy, rfl⟩ := hxτ
      exact ⟨(P).mem_support.mpr ((P).isComplete_iff.mp hP _),
        ((mem_chart_preimage_iff Φ m h b hm k).mp hξ).2 y hy⟩
    have hcones := (Q).cones_eq_of_subset_of_support_subset
      (chart_product_cones_subset Φ m h b hm k hcorners) hs
    rw [hcones, mapEquiv_cones]
    have hinj : Function.Injective M := Submodule.map_injective_of_injective (E).injective
    exact hinj.injOn.mem_image_iff (Set.subset_univ _) (Set.mem_univ σ)

include hm in
private theorem snd_comp_chartFanEquiv
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) :
    (FanHom.snd P A[k]).comp (chartFanEquiv Φ m h b hm k hcorners).toFanHom = g := by
  apply FanHom.ext
  ext x j
  simp [chartFanEquiv, hm]

include hm in
private theorem denseTorusι_comp_chart_firstProjection
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) (hU : Nonempty (U).cones) :
    (U).denseTorusι hU ≫ (chartFanEquiv Φ m h b hm k hcorners).toFanHom.algebraicMap ≫
      (FanHom.fst P A[k]).algebraicMap ≫ projectiveLineToricIso.hom =
        projectiveLine.polynomialPoint ℂ (algebraMap ℂ _) 0
          (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm
            (b.coord 0).toAddMonoidHom))) := by
  let e := chartFanEquiv Φ m h b hm k hcorners
  let q := (FanHom.fst P A[k]).comp e.toFanHom
  obtain ⟨hn, hq⟩ := q.exists_eq_characterFanHom
    (b.coord 0).toAddMonoidHom (fun x j ↦ by simp [q, e, chartFanEquiv])
  rw [← Category.assoc (chartFanEquiv Φ m h b hm k hcorners).toFanHom.algebraicMap,
    ← FanHom.algebraicMap_comp]
  -- The first projection uses the character of the first dual vector of the chosen basis.
  change (U).denseTorusι hU ≫ q.algebraicMap ≫ projectiveLineToricIso.hom = _
  rw [hq, ← characterRuling_def, denseTorusι_comp_characterRuling]

include hm in
/-- Over the polynomial chart `k`, the ruling of the second coordinate of `b`
is a product with the projective line if the fan contains both quadrants
adjacent to the signed second basis ray for that chart. On the dense torus
the fiber coordinate is the monomial of the first dual basis vector. -/
theorem exists_characterRuling_affine_chart_product
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) :
    let h₀ : Nonempty Φ.cones := ⟨⟨_, hcorners 0⟩⟩
    let f := Φ.characterRuling m h
    let c := projectiveLine.polynomialChartι ℂ k
    ∃ (u : pullback f c ⟶ L) (t : Φ.denseTorus ⟶ pullback f c),
      IsPullback u (pullback.snd f c) (L ↘ S)
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))) ∧
      t ≫ pullback.fst f c = Φ.denseTorusι h₀ ∧
      t ≫ u = projectiveLine.polynomialPoint ℂ (algebraMap ℂ _) 0
        (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm
          (b.coord 0).toAddMonoidHom))) := by
  intro h₀ f c
  let F := chartFanEquiv Φ m h b hm k hcorners
  let ιU := Φ.subfanInclusion _ ((charMap).preimageCones_subset F[k])
    ((charMap).preimageCones_closedUnderFaces F[k] (chart_faces_closed k))
  have hpre := (charMap).isPullback_preimageSubfan_algebraicMap F[k] (chart_faces_subset k)
    (chart_faces_closed k)
  have hbase : IsPullback (ι[k]).algebraicMap (chartIso k).hom
      projectiveLineToricIso.hom (projectiveLine.polynomialChartι ℂ k) :=
    IsPullback.of_vert_isIso ⟨(chartIso_hom_comp_polynomialChartι k).symm⟩
  have hchart : IsPullback ιU.algebraicMap ((g).algebraicMap ≫ (chartIso k).hom)
      (Φ.characterRuling m h) (projectiveLine.polynomialChartι ℂ k) := by
    simpa only [characterRuling_def] using hpre.paste_vert hbase
  let e := hchart.isoPullback.symm ≪≫ asIso F.toFanHom.algebraicMap
  let u := e.hom ≫ (FanHom.fst P A[k]).algebraicMap ≫ projectiveLineToricIso.hom
  have hbot : (⊥ : PointedCone ℝ V) ∈ (U).cones :=
    (mem_chart_preimage_iff Φ m h b hm k).2 ⟨Φ.bot_mem h₀.some.property, by
      intro x hx
      rw [(Submodule.mem_bot (Nonneg ℝ)).mp hx, map_zero]
      exact zero_mem _⟩
  let hU : Nonempty (U).cones := ⟨⟨⊥, hbot⟩⟩
  refine ⟨u, (U).denseTorusι hU ≫ hchart.isoPullback.hom, ?_, ?_, ?_⟩
  · refine ((P).isPullback_fst_snd_algebraicMap A[k]).of_iso' e projectiveLineToricIso.symm
      (chartIso k).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [u]
    · rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, ← FanHom.algebraicMap_comp,
        snd_comp_chartFanEquiv, ← cancel_mono (chartIso k).hom]
      simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id,
        IsPullback.isoPullback_inv_snd]
      rfl
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← cancel_epi projectiveLineToricIso.hom, Iso.hom_inv_id_assoc,
        ← Fan.algebraicRealization_over, CategoryTheory.comp_over]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← cancel_epi (chartIso k).hom,
        Iso.hom_inv_id_assoc, ← projectiveLine.polynomialChartι_over ℂ k,
        chartIso_hom_comp_polynomialChartι_assoc, ← Fan.algebraicRealization_over,
        CategoryTheory.comp_over, CategoryTheory.comp_over]
  · rw [Category.assoc, hchart.isoPullback_hom_fst, denseTorusι_eq_affineToricChartι _ _ hbot,
      affineToricChartι_comp_subfanInclusion_algebraicMap, ← denseTorusι_eq_affineToricChartι]
  · simp only [u, e, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact denseTorusι_comp_chart_firstProjection Φ m h b hm k hcorners hU

variable (a : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, a • b 0 - b 1])

include hΦ hc hr in
/-- The character ruling of a complete regular Hirzebruch fan is a product over
each of the two standard affine charts of the base projective line. The first
fiber coordinate is the monomial of the first dual basis vector. In the
second chart its exponent gains `a` times the second dual basis vector. -/
theorem exists_hirzebruch_characterRuling_affine_chart_product :
    let f := Φ.characterRuling (b.coord 1).toAddMonoidHom
      (nonneg_or_nonpos_hirzebruch_ruling_character b a r hr)
    let c := projectiveLine.polynomialChartι ℂ k
    let n := (b.coord 0 + (if k = 0 then 0 else a) • b.coord 1).toAddMonoidHom
    ∃ (u : pullback f c ⟶ L) (t : Φ.denseTorus ⟶ pullback f c),
      IsPullback u (pullback.snd f c) (L ↘ S)
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))) ∧
      t ≫ pullback.fst f c = Φ.denseTorusι hc.nonempty_cones ∧
      t ≫ u = projectiveLine.polynomialPoint ℂ (algebraMap ℂ _) 0
        (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm n))) := by
  intro f c n
  let h := nonneg_or_nonpos_hirzebruch_ruling_character b a r hr
  rcases eq_or_ne k 0 with rfl | hk
  · simpa [f, c, n] using Φ.exists_characterRuling_affine_chart_product _ h b rfl 0
      (by simpa using fun j ↦ Φ.hirzebruch_chart_corners b a r hr hΦ hc j 0)
  · let e := LinearEquiv.transvection (f := (-a) • b.coord 1) (v := b 0)
        (by simp [Basis.coord_apply])
    let d := b.map e
    have hd₀ : d 0 = b 0 := by
      simp [d, e, LinearMap.transvection.apply, Basis.coord_apply]
    have hd₁ : d 1 = b 1 - a • b 0 := by
      simp [d, e, LinearMap.transvection.apply, Basis.coord_apply, sub_eq_add_neg]
    have hcoord : (b.coord 1).toAddMonoidHom = (d.coord 1).toAddMonoidHom := by
      apply congrArg LinearMap.toAddMonoidHom
      apply d.ext
      intro j
      simp only [Basis.coord_apply, Basis.repr_self]
      fin_cases j
      · simp [hd₀]
      · simp [hd₁]
    have hfirst : (d.coord 0).toAddMonoidHom = n := by
      dsimp only [n]
      apply congrArg LinearMap.toAddMonoidHom
      apply d.ext
      intro j
      simp only [Basis.coord_apply, Basis.repr_self, ite_eq_right hk, LinearMap.add_apply,
        LinearMap.smul_apply]
      fin_cases j
      · simp [hd₀]
      · simp [hd₁]
    have hcorners (j : Fin 2) : hull ℝ {i (if j = 0 then d 0 else -d 0),
        i (if k = 0 then d 1 else -d 1)} ∈ Φ.cones := by
      simpa only [hd₀, ite_eq_right hk, hd₁, neg_sub] using
        Φ.hirzebruch_chart_corners b a r hr hΦ hc j k
    simpa only [f, c, hfirst] using
      Φ.exists_characterRuling_affine_chart_product _ h d hcoord k hcorners

end TauCeti.Toric.Fan
