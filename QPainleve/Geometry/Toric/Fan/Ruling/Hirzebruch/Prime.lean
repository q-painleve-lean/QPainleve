/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Curves.Morphism
import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.WeilDivisor.Basic
import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf

/-!
# Prime curves under the Hirzebruch ruling

The Hirzebruch Picard coordinates compute the degree of the ruling on prime
curves and characterize section curves and scheme-theoretic fibers.
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [IsAlgClosed K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => (Φ.finiteFanScheme K)
local notation "S" => Spec (CommRingCat.of K)
local notation "C" => Φ.hirzebruchPicardBasis K b e hΦ r hr
local notation "P" p:arg =>
  Additive.ofMul
    (@primeDivisorClass X _ _ (Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ) p)
variable [((Φ.finiteFanScheme K)).IsProjectiveOver K]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme K) ↘ Spec (CommRingCat.of K))]

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "q" =>
  Φ.characterRuling K m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "H" => Additive.toMul (AddEquiv.symm (projectiveLine.picardDegreeEquiv K) 1)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "g[" p "]" => Scheme.IdealSheafData.subschemeι (I[p]) ≫ q

include hc in
/-- The degree of the ruling restricted to a prime curve, measured by pulling back the
degree-one line class, is the section coefficient of the curve. -/
theorem eulerDegree_hirzebruch_ruling_prime (p : CodimensionOnePoint X) :
    eulerDegree K (pullback g[p] H) = (C).repr (P p) 1 := by
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  rw [← intersectionNumber_def, ← intersectionNumber_pullback,
    ← Φ.hirzebruchPicardBasis_zero_eq_pullback_characterRuling K b e hΦ r hr,
    ← Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber K hdim,
    Chow.classIntersectionNumber_comm, ← toMul_ofMul (primeDivisorClass p),
    ← Chow.intersectionBilinForm_apply]
  exact (Φ.hirzebruchPicardBasis_intersection_repr K b e hΦ r hr hc (P p)).1

include hc in
/-- A prime curve contained in a rational fiber of the Hirzebruch ruling has
fiber degree zero. -/
theorem hirzebruch_fiber_degree_eq_zero_of_mem_ruling_fiber {p : CodimensionOnePoint X}
    {y : S ⟶ projectiveLine K} (hy : y ≫ (projectiveLine K ↘ S) = 𝟙 S)
    (hp : (p : X) ∈ (y.ker.comap q).support) : (C).repr (P p) 1 = 0 := by
  let f := g[p]
  have : IsClosedImmersion y := y.isClosedImmersion_of_comp_eq_id hy
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let : (I[p]).subscheme.IsProjectiveOver K :=
    Scheme.IsProjectiveOver.of_isClosedImmersion K (I[p]).subschemeι
  let : (I[p]).subscheme.IsCurveOver K := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme K hdim p⟩
  have hsub : Set.range f ⊆ Set.range y := by
    rintro _ ⟨x, rfl⟩
    have hmem : (I[p]).subschemeι x ∈ (y.ker.comap q).support := by
      apply closure_minimal (Set.singleton_subset_iff.mpr hp)
        ((y.ker.comap q).support).isClosed'
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
  rw [← Φ.eulerDegree_hirzebruch_ruling_prime K b e hΦ hc r hr p, ← intersectionNumber_def]
  exact intersectionNumber_eq_zero_of_subsingleton_image _ f hf

omit [IsAlgClosed K] in
/-- The dominant restriction of the Hirzebruch ruling to a prime curve is finite and flat,
with rank given by the degree of the pulled-back degree-one line class. -/
theorem hirzebruch_ruling_prime_degree_of_isDominant
    (p : CodimensionOnePoint X) [IsDominant g[p]] :
    IsFinite g[p] ∧ Flat g[p] ∧
      ∀ y : projectiveLine K, eulerDegree K (pullback g[p] H) = (g[p].finrank y : ℤ) := by
  let Y := (I[p]).subscheme
  have : Y.IsProjectiveOver K := Scheme.IsProjectiveOver.of_isClosedImmersion K (I[p]).subschemeι
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Y.IsCurveOver K := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme K hdim p⟩
  let : (projectiveLine K).IsCurveOver K := projectiveLine.isCurveOver K
  let : ∀ z : projectiveLine K, ValuationRing ((projectiveLine K).presheaf.stalk z) :=
    Scheme.IsCurveOver.valuationRing_stalk K _
  have : IsFinite g[p] := g[p].isFinite_of_isDominant_of_isCurveOver (k := K)
  have : Flat g[p] := g[p].flat_of_isDominant_of_valuationRing
  have (j : ℕ) := Scheme.Modules.moduleFinite_cohomology_of_isProjectiveOver K
    (InvertibleSheaf.trivial Y).obj j
  refine ⟨inferInstance, inferInstance, fun y ↦ ?_⟩
  rw [eulerDegree_pullback_of_isDominant K g[p],
    g[p].finrank_eq_finrank_fieldRange_functionFieldMap]
  have hH : eulerDegree K H = 1 := by
    simpa only [projectiveLine.picardDegreeEquiv_apply] using
      (projectiveLine.picardDegreeEquiv K).apply_symm_apply 1
  rw [hH, mul_one]

include hc in
/-- A prime curve of fiber degree one maps isomorphically to the base of the Hirzebruch ruling. -/
theorem isIso_hirzebruch_ruling_prime_of_degree_one (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 1 = 1) : IsIso g[p] := by
  let Y := (I[p]).subscheme
  have : Y.IsProjectiveOver K := Scheme.IsProjectiveOver.of_isClosedImmersion K (I[p]).subschemeι
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Y.IsCurveOver K := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme K hdim p⟩
  have hdeg := (eulerDegree_hirzebruch_ruling_prime K b e hΦ hc r hr p).trans hp
  have : IsDominant g[p] := by
    apply isDominant_iff_genericPoint_eq.mpr
    by_contra h
    have hd : topologicalKrullDim (projectiveLine K) = 1 :=
      Scheme.IsCurveOver.topologicalKrullDim_eq_one K
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
    have hz := intersectionNumber_eq_zero_of_subsingleton_image (k := K) H g[p] hrange
    rw [intersectionNumber_def, hdeg] at hz
    exact one_ne_zero hz
  obtain ⟨hfinite, hflat, hrank⟩ := hirzebruch_ruling_prime_degree_of_isDominant K b e r hr p
  let := hfinite
  let := hflat
  refine (g[p].isIso_iff_finrank_eq).mpr (funext fun y ↦ ?_)
  exact_mod_cast (hrank y).symm.trans hdeg

private theorem primeClass_eq_fiber_of_le (p : CodimensionOnePoint X)
    (hp : (C).repr (P p) 1 = 0) (W : SchemeWeilDivisor X)
    (hle : Finsupp.single p 1 ≤ W)
    (hW : let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
      Scheme.CartierDivisor.weilToLineBundleClassHom X W = C 0) :
    P p = C 0 := by
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  let cl := Scheme.CartierDivisor.weilToLineBundleClassHom X
  let a := (C).repr (P p) 0
  have hrepr : P p = a • C 0 := by
    simpa only [Fin.sum_univ_two, hp, zero_smul, add_zero] using ((C).sum_repr (P p)).symm
  have hs : cl (Finsupp.single p 1) = P p := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_single, one_smul, ← primeDivisorClass_def]
  obtain ⟨A, hA⟩ := Scheme.exists_isAmple_of_isProjectiveOver X K
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let B := Chow.classIntersectionBilinForm K hdim (Additive.ofMul A)
  have hpos (a : CodimensionOnePoint X) : 0 < B (P a) := by
    simpa only [B, Chow.classIntersectionBilinForm_apply, toMul_ofMul] using
      Chow.classIntersectionNumber_primeDivisorClass_pos_of_isAmple K hdim hA a
  have hres : 0 ≤ B (cl (W - Finsupp.single p 1)) :=
    Chow.classIntersectionBilinForm_nonneg_of_mem_effectiveClasses K hdim
      (fun a ↦ (hpos a).le)
      (Scheme.mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨_, sub_nonneg.mpr hle, rfl⟩)
  have hclass : cl W = C 0 := hW
  rw [map_sub, hclass, hs, map_sub, sub_nonneg] at hres
  have hp_pos := hpos p
  have hF : 0 < B (C 0) := hp_pos.trans_le hres
  rw [hrepr, map_zsmul, zsmul_eq_mul, Int.cast_id] at hp_pos hres
  have ha₀ := pos_of_mul_pos_left hp_pos hF.le
  have ha₁ : a ≤ 1 := by
    exact (mul_le_mul_iff_left₀ hF).mp (by simpa only [one_mul] using hres)
  have ha : a = 1 := by omega
  exact hrepr.trans (by rw [ha, one_smul])

/-- A vertical prime curve over a rational point of a Hirzebruch ruling
has fiber class and equals the scheme-theoretic fiber over that point. -/
theorem hirzebruch_ruling_fiber_of_degree_zero
    (p : CodimensionOnePoint X) (hp : (C).repr (P p) 1 = 0)
    {y : Spec (CommRingCat.of K) ⟶ projectiveLine K}
    (hy : y ≫ (projectiveLine K ↘ S) = 𝟙 S) (hz : (p : X) ∈ (y.ker.comap q).support) :
    P p = C 0 ∧ I[p] = y.ker.comap q := by
  let := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hm := hirzebruch_ruling_character_ne_zero b
  let hI := Φ.isEffectiveCartier_characterRuling_fiber K m
    (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr) hm y hy
  have hyC := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension y hy)
    |>.isEffectiveCartier
  have hyH : (LineBundleClass.mk hyC.toInvertibleSheaf)⁻¹ = H := by
    apply Additive.ofMul.injective
    apply (projectiveLine.picardDegreeEquiv K).injective
    rw [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul, projectiveLine.eulerDegree_inv,
      LineBundleClass.eulerDegree_mk, y.eulerDegree_ker_of_smooth hy]
    simp only [ofMul_toMul, AddEquiv.apply_symm_apply, neg_neg]
  have hclass : (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ = (Additive.toMul (C 0)) := by
    rw [Φ.hirzebruchPicardBasis_zero_eq_pullback_characterRuling K b e hΦ r hr, ← hyH, pullback_inv,
      hyC.pullback_mk_toInvertibleSheaf hI]
  let : IsNormalScheme (Φ.finiteFanScheme K) :=
    Φ.isNormalScheme_finiteFanScheme K hΦ
  let W := hI.toCartierDivisor.toWeilDivisor
  let cl := Scheme.CartierDivisor.weilToLineBundleClassHom X
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hI.isEffective_toCartierDivisor
  have hpW : 0 < W p := lt_of_le_of_ne (hW p)
    (fun h ↦ (hI.coeff_toWeilDivisor_eq_zero_iff p).mp h.symm hz)
  have hle := WeilDivisor.single_one_le_of_coeff_pos hW hpW
  have hcl : cl W = C 0 := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
      hI.toLineBundleClass_toCartierDivisor, hclass, ofMul_toMul]
  have hprime := primeClass_eq_fiber_of_le K b e hΦ r hr p hp W hle hcl
  have hzero : cl (W - Finsupp.single p 1) = 0 := by
    rw [map_sub, Scheme.CartierDivisor.weilToLineBundleClassHom_single, one_smul,
      ← primeDivisorClass_def, hprime, hcl, sub_self]
  have hW_eq := (Chow.weilToLineBundleClassHom_eq_zero_iff_of_nonneg K hdim
    (sub_nonneg.mpr hle)).mp hzero
  refine ⟨hprime, ((hI.toCartierDivisor_eq_iff
    (isEffectiveCartier_vanishingIdeal_closure_singleton p.property)).mp ?_).symm⟩
  apply Scheme.CartierDivisor.toWeilDivisor_injective
  rw [toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton,
    ← one_smul ℤ (WeilDivisor.ofPoint p), ← WeilDivisor.single_eq_zsmul_ofPoint]
  exact sub_eq_zero.mp hW_eq

include hc in
/-- A prime curve of fiber degree zero has fiber class and is the
scheme-theoretic fiber of the Hirzebruch ruling over a rational point. -/
theorem exists_hirzebruch_ruling_fiber_of_degree_zero
    (p : CodimensionOnePoint X) (hp : (C).repr (P p) 1 = 0) :
    ∃ y : Spec (CommRingCat.of K) ⟶ projectiveLine K,
      y ≫ (projectiveLine K ↘ S) = 𝟙 S ∧ P p = C 0 ∧ I[p] = y.ker.comap q := by
  let Y := (I[p]).subscheme
  have hdeg₀ := (eulerDegree_hirzebruch_ruling_prime K b e hΦ hc r hr p).trans hp
  let y₀ := q (p : X)
  have hgeneric : g[p] (genericPoint Y) = y₀ := by
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_vanishingIdeal_closure_singleton]
  have hy₀ : IsClosed ({y₀} : Set (projectiveLine K)) := by
    have hd : topologicalKrullDim (projectiveLine K) = 1 :=
      Scheme.IsCurveOver.topologicalKrullDim_eq_one K
    apply TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint hd.le
    intro hy
    have : IsDominant g[p] := isDominant_iff_genericPoint_eq.mpr (hgeneric.trans hy)
    obtain ⟨hfinite, hflat, hrank⟩ := hirzebruch_ruling_prime_degree_of_isDominant K b e r hr p
    let := hfinite
    let := hflat
    have hn : g[p].finrank y₀ = 0 := by exact_mod_cast (hrank y₀).symm.trans hdeg₀
    exact ((g[p]).finrank_eq_zero_iff_notMem_range y₀).mp hn ⟨genericPoint Y, hgeneric⟩
  let y := pointOfClosedPoint (projectiveLine K ↘ S) y₀ hy₀
  have hy : y ≫ (projectiveLine K ↘ S) = 𝟙 S :=
    pointOfClosedPoint_comp (projectiveLine K ↘ S) y₀ hy₀
  refine ⟨y, hy, ?_⟩
  have hz : (p : X) ∈ (y.ker.comap q).support := by
    rw [← SetLike.mem_coe, support_comap, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
      Scheme.Hom.support_ker]
    exact subset_closure ⟨IsLocalRing.closedPoint K, pointOfClosedPoint_apply _ _ _ _⟩
  exact hirzebruch_ruling_fiber_of_degree_zero K b e hΦ r hr p hp hy hz

end TauCeti.Toric.Fan
