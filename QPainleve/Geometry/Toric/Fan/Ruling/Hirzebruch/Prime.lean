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
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Curves.Morphism
import QPainleve.AlgebraicGeometry.IntersectionNumber.CurveImage
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
variable [(Φ.algebraicRealization).IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]

local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "q" =>
  Φ.characterRuling m (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "H" => Additive.toMul (AddEquiv.symm (projectiveLine.picardDegreeEquiv ℂ) 1)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)
local notation "g[" p "]" => Scheme.IdealSheafData.subschemeι (I[p]) ≫ q

include hc in
/-- The degree of the ruling restricted to a prime curve, measured by pulling back the
degree-one line class, is the section coefficient of the curve. -/
theorem eulerDegree_hirzebruch_ruling_prime (p : CodimensionOnePoint X) :
    eulerDegree ℂ (pullback g[p] H) = (C).repr (P p) 1 := by
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  rw [← intersectionNumber_def, ← intersectionNumber_pullback,
    ← Φ.hirzebruchPicardBasis_zero_eq_pullback_characterRuling b e hΦ r hr,
    ← Chow.classIntersectionNumber_primeDivisorClass_eq_intersectionNumber ℂ hdim,
    Chow.classIntersectionNumber_comm, ← toMul_ofMul (primeDivisorClass p),
    ← Chow.intersectionBilinForm_apply]
  exact (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (P p)).1

include hc in
/-- A prime curve contained in a rational fiber of the Hirzebruch ruling has
fiber degree zero. -/
theorem hirzebruch_fiber_degree_eq_zero_of_mem_ruling_fiber {p : CodimensionOnePoint X}
    {y : S ⟶ projectiveLine ℂ} (hy : y ≫ (projectiveLine ℂ ↘ S) = 𝟙 S)
    (hp : (p : X) ∈ (y.ker.comap q).support) : (C).repr (P p) 1 = 0 := by
  let f := g[p]
  have : IsClosedImmersion y := y.isClosedImmersion_of_comp_eq_id hy
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let : (I[p]).subscheme.IsProjectiveOver ℂ :=
    Scheme.IsProjectiveOver.of_isClosedImmersion ℂ (I[p]).subschemeι
  let : (I[p]).subscheme.IsCurveOver ℂ := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme ℂ hdim p⟩
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
  rw [← Φ.eulerDegree_hirzebruch_ruling_prime b e hΦ hc r hr p, ← intersectionNumber_def]
  exact intersectionNumber_eq_zero_of_subsingleton_image _ f hf

/-- The dominant restriction of the Hirzebruch ruling to a prime curve is finite and flat,
with rank given by the degree of the pulled-back degree-one line class. -/
theorem hirzebruch_ruling_prime_degree_of_isDominant
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
/-- A prime curve of fiber degree one maps isomorphically to the base of the Hirzebruch ruling. -/
theorem isIso_hirzebruch_ruling_prime_of_degree_one (p : CodimensionOnePoint X)
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

/-- A prime curve in the fiber class that lies over a given rational point equals
that scheme-theoretic fiber. -/
theorem eq_hirzebruch_ruling_fiber_of_prime_class_eq
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
/-- A prime curve in the fiber class is the scheme-theoretic fiber over a rational point
of the Hirzebruch ruling. -/
theorem exists_hirzebruch_ruling_fiber_of_prime_class_eq
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

end TauCeti.Toric.Fan
