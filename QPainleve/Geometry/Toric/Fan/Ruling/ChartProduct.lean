/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.AffineChart

import QPainleve.Geometry.Toric.Fan.Equiv
import QPainleve.Geometry.Toric.BaseChange.Product
import QPainleve.Geometry.Toric.BaseChange.Subfan

/-!
# Product charts of a toric character ruling

Two adjacent quadrants in a rank-two fan suffice to identify the preimage of
the corresponding affine base chart with a projective-line product. The
first dual basis vector gives the fiber coordinate on the dense torus.

The construction uses the product of toric fans and the inverse image of an
open subfan. See Fulton, *Introduction to Toric Varieties*, §1.4 and §2.1.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable (K : Type) [CommRing K]

local notation "S" => Spec (CommRingCat.of K)
local notation "L" => projectiveLine K
local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "A[" k "]" => projectiveLineAffineFan k
local notation "F[" k "]" => Fan.cones (A[k])
local notation "ι[" k "]" => projectiveLineAffineFanInclusion k
local notation "R[" k "]" => projectiveLineAffineRay k

private theorem chart_support (k : Fin 2) : (A[k]).support = R[k] := by
  rw [projectiveLineAffineFan, ← (P).ofCone_eq_subfan (projectiveLineAffineRay_mem k),
    Fan.support_ofCone]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom) (k : Fin 2)

local notation "charMap" => Φ.characterFanHom m h
local notation "U" => FanHom.preimageSubfan charMap F[k] (Fan.mem_of_isFaceOf (A[k]))
local notation "g" =>
  FanHom.restrictToPreimage charMap F[k] (projectiveLineAffineFan_cones_subset k)
    (Fan.mem_of_isFaceOf (A[k]))
local notation "Q" => Fan.prod P A[k]
local notation "W" => (Fin 1 → ℝ)
local notation "torusChart(" G "," h₀ ")" =>
  Fan.affineChartι K G (Subtype.mk ⊥ (Fan.bot_mem G (Subtype.property (Nonempty.some h₀))))
local notation "toricLine" => (projectiveLineToricIso K)

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
    σ ∈ (U).cones ↔ σ ∈ Φ.cones ∧ (∀ x ∈ σ, (E x).2 ∈ R[k]) := by
  rw [Fan.subfan_cones]
  constructor
  · intro hpre
    have hσ := (charMap).preimageCones_subset F[k] hpre
    have hface := mem_projectiveLineAffineFan_cones.mp
      (((charMap).mem_preimageCones_iff F[k] hσ).mp hpre)
    refine ⟨hσ, fun x hx ↦ hface.le ?_⟩
    rw [← characterFanHom_realMap_eq_chartCoordinates_snd Φ m h b hm k x]
    exact (charMap).map_le_leastCone hσ ⟨x, hx, rfl⟩
  · rintro ⟨hσ, hmap⟩
    refine ((charMap).mem_preimageCones_iff F[k] hσ).mpr
      (mem_projectiveLineAffineFan_cones.mpr
        ((P).isFaceOf_of_le (projectiveLineAffineRay_mem k) ((charMap).leastCone_mem hσ) ?_))
    apply (charMap).leastCone_le hσ (projectiveLineAffineRay_mem k)
    rintro _ ⟨x, hx, rfl⟩
    exact (characterFanHom_realMap_eq_chartCoordinates_snd Φ m h b hm k x).symm ▸ hmap x hx

private theorem map_chart_corner (j : Fin 2) :
    M (hull ℝ {i (if j = 0 then b 0 else -b 0), i (if k = 0 then b 1 else -b 1)}) =
      R[j].prod R[k] := by
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
  have hs (l : Fin 2) : R[l] = hull ℝ {(if l = 0 then 1 else -1 : W)} := by
    unfold projectiveLineAffineRay
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
  have hmax (j : Fin 2) : R[j].prod R[k] ∈ ((U).mapEquiv (Q).lattice coordZ).cones := by
    rw [mapEquiv_cones, ← map_chart_corner Φ m h b k j]
    refine Set.mem_image_of_mem _ ((mem_chart_preimage_iff Φ m h b hm k).2
      ⟨hcorners j, fun x hx ↦ ?_⟩)
    have hmem : E x ∈ M (hull ℝ {i (if j = 0 then b 0 else -b 0),
        i (if k = 0 then b 1 else -b 1)}) := ⟨x, hx, rfl⟩
    rw [map_chart_corner Φ m h b k j] at hmem
    exact hmem.2
  intro σ hσ
  obtain ⟨a, ha, c, hc, rfl⟩ := (Fan.mem_prod_cones _ _).1 hσ
  have hc' : c.IsFaceOf R[k] := mem_projectiveLineAffineFan_cones.mp hc
  rw [projectiveSpace_finOne_eq_projectiveLineFan, mem_projectiveLineFan_cones] at ha
  have ha' : ∃ j : Fin 2, a.IsFaceOf R[j] := by
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, ((P).isToricCone (projectiveLineAffineRay_mem 0)).salient.bot_isFaceOf⟩
    · exact ⟨0, .refl _⟩
    · exact ⟨1, .refl _⟩
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
    torusChart(U,hU) ≫
      (chartFanEquiv Φ m h b hm k hcorners).toFanHom.finiteFanSchemeHom K ≫
      (FanHom.fst P A[k]).finiteFanSchemeHom K ≫ (toricLine).hom =
        projectiveLine.polynomialPoint K (algebraMap K _) 0
          (AddMonoidAlgebra.single ⟨(b.coord 0).toAddMonoidHom, by simp⟩ 1) := by
  let e := chartFanEquiv Φ m h b hm k hcorners
  let q := (FanHom.fst P A[k]).comp e.toFanHom
  obtain ⟨hn, hq⟩ := q.exists_eq_characterFanHom
    (b.coord 0).toAddMonoidHom (fun x j ↦ by simp [q, e, chartFanEquiv])
  rw [← Category.assoc ((chartFanEquiv Φ m h b hm k hcorners).toFanHom.finiteFanSchemeHom K),
    ← FanHom.finiteFanSchemeHom_comp K]
  -- The first projection uses the character of the first dual vector of the chosen basis.
  change torusChart(U,hU) ≫ q.finiteFanSchemeHom K ≫ (toricLine).hom = _
  rw [hq, ← characterRuling_def K, denseTorusι_comp_characterRuling K _ _ _ hU]

include hm in
/-- Over the polynomial chart `k`, the ruling of the second coordinate of `b`
is a product with the projective line if the fan contains both quadrants
adjacent to the signed second basis ray for that chart. On the dense torus
the fiber coordinate is the monomial of the first dual basis vector. -/
theorem exists_characterRuling_affine_chart_product
    (hcorners : ∀ j : Fin 2, hull ℝ {i (if j = 0 then b 0 else -b 0),
      i (if k = 0 then b 1 else -b 1)} ∈ Φ.cones) :
    let h₀ : Nonempty Φ.cones := ⟨⟨_, hcorners 0⟩⟩
    let f := Φ.characterRuling K m h
    let c := projectiveLine.polynomialChartι K k
    ∃ (u : pullback f c ⟶ L) (t : affineChart K Φ.lattice ⊥ ⟶ pullback f c),
      IsPullback u (pullback.snd f c) (L ↘ S)
        (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ∧
      t ≫ pullback.fst f c = torusChart(Φ,h₀) ∧
      t ≫ u = projectiveLine.polynomialPoint K (algebraMap K _) 0
        (AddMonoidAlgebra.single ⟨(b.coord 0).toAddMonoidHom, by simp⟩ 1) := by
  intro h₀
  dsimp only
  let F := chartFanEquiv Φ m h b hm k hcorners
  let ιU := Φ.subfanInclusion _ ((charMap).preimageCones_subset F[k])
    ((charMap).preimageCones_closedUnderFaces F[k] (A[k]).mem_of_isFaceOf)
  have hpre := (charMap).isPullback_preimageSubfan_finiteFanSchemeHom K F[k]
    (projectiveLineAffineFan_cones_subset k) (A[k]).mem_of_isFaceOf
  have hbase : IsPullback ((ι[k]).finiteFanSchemeHom K) (projectiveLineAffineFanIso K k).hom
      (toricLine).hom (projectiveLine.polynomialChartι K k) :=
    IsPullback.of_vert_isIso ⟨by
      rw [projectiveLineAffineFanIso_hom_comp_polynomialChartι, projectiveLineAffineFanι_def]⟩
  have hchart : IsPullback (ιU.finiteFanSchemeHom K)
      ((g).finiteFanSchemeHom K ≫ (projectiveLineAffineFanIso K k).hom)
      (Φ.characterRuling K m h) (projectiveLine.polynomialChartι K k) := by
    simpa only [characterRuling_def K] using hpre.paste_vert hbase
  let e := hchart.isoPullback.symm ≪≫ asIso (F.toFanHom.finiteFanSchemeHom K)
  let u := e.hom ≫ ((FanHom.fst P A[k]).finiteFanSchemeHom K) ≫ (toricLine).hom
  have hbot : (⊥ : PointedCone ℝ V) ∈ (U).cones :=
    (mem_chart_preimage_iff Φ m h b hm k).2 ⟨Φ.bot_mem h₀.some.property, by
      intro x hx
      rw [(Submodule.mem_bot (Nonneg ℝ)).mp hx, map_zero]
      exact zero_mem _⟩
  let hU : Nonempty (U).cones := ⟨⟨⊥, hbot⟩⟩
  refine ⟨u, torusChart(U,hU) ≫ hchart.isoPullback.hom, ?_, ?_, ?_⟩
  · refine ((P).isPullback_fst_snd_finiteFanSchemeHom K A[k]).of_iso' e (toricLine).symm
      (projectiveLineAffineFanIso K k).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [u]
    · rw [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
        ← FanHom.finiteFanSchemeHom_comp K, snd_comp_chartFanEquiv,
        ← cancel_mono (projectiveLineAffineFanIso K k).hom]
      simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
      exact hchart.isoPullback_inv_snd
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← cancel_epi (toricLine).hom, Iso.hom_inv_id_assoc,
        ← Fan.finiteFanScheme_over K, CategoryTheory.comp_over]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
        ← cancel_epi (projectiveLineAffineFanIso K k).hom, Iso.hom_inv_id_assoc,
        ← projectiveLine.polynomialChartι_over K k,
        projectiveLineAffineFanIso_hom_comp_polynomialChartι_assoc, projectiveLineAffineFanι_def,
        Category.assoc, ← Fan.finiteFanScheme_over K,
        CategoryTheory.comp_over, CategoryTheory.comp_over]
  · rw [Category.assoc, hchart.isoPullback_hom_fst,
      affineChartι_comp_subfanInclusion_finiteFanSchemeHom]
  · simp only [u, e, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact denseTorusι_comp_chart_firstProjection K Φ m h b hm k hcorners hU

end TauCeti.Toric.Fan
