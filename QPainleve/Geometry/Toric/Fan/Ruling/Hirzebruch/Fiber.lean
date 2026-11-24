/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Trivialization
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Picard.FiberDegree
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Fibers of a toric Hirzebruch ruling

The affine charts identify each scheme-theoretic fiber with the projective line over its
residue field. Over a closed point the section divisor supplies a degree-one polarization.
These are the fiber inputs for comparing the ruling with the projectivization of a rank-two
direct image.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "PL" => projectiveLine ℂ
local notation "m" => LinearMap.toAddMonoidHom (b.coord 1)
local notation "h" => nonneg_or_nonpos_hirzebruch_ruling_character b e r hr
local notation "q" => Φ.characterRuling m h
local notation "U[" k "]" => Fan.algebraicRealization (projectiveLineAffineFan k)
local notation "s[" k "]" => Fan.algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "j[" k "]" => projectiveLineAffineFanι k

include hΦ hc in
/-- The Hirzebruch ruling is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_hirzebruch_characterRuling :
    SmoothOfRelativeDimension 1 q := by
  let : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @SmoothOfRelativeDimension 1)
  let : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{0} 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  let cover : Scheme.OpenCover PL := Scheme.Cover.mkOfCovers (Fin 2)
    (fun k ↦ U[k]) projectiveLineAffineFanι exists_projectiveLineAffineFanι_apply_eq
  refine IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension 1) cover fun k ↦ ?_
  let a := hirzebruchRulingAffineIso b e r hr hΦ hc k
  have hs : SmoothOfRelativeDimension 1 (pullback.snd (PL ↘ S) s[k]) :=
    inferInstance
  have ht : a.hom ≫ pullback.snd (PL ↘ S) s[k] = pullback.snd q j[k] :=
    hirzebruchRulingAffineIso_hom_snd b e r hr hΦ hc k
  have hs' : SmoothOfRelativeDimension 1 (pullback.snd q j[k]) :=
    ht ▸ (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
      a.hom _).mpr hs
  exact hs'

include hΦ hc in
private theorem exists_isPullback_hirzebruch_ruling_of_range {Z : Scheme}
    (p : Z ⟶ PL) (k : Fin 2) (hp : Set.range p ⊆ Set.range j[k]) :
    ∃ u : pullback (PL ↘ S) (p ≫ PL ↘ S) ⟶ X,
      IsPullback u (pullback.snd _ _) q p := by
  let l := IsOpenImmersion.lift j[k] p hp
  have hl : l ≫ j[k] = p := IsOpenImmersion.lift_fac _ _ _
  have hj : l ≫ s[k] = p ≫ PL ↘ S := by
    rw [← hl, Category.assoc, projectiveLineAffineFanι_def, Category.assoc, comp_over,
      comp_over, algebraicRealization_over]
  let a := hirzebruchRulingAffineIso b e r hr hΦ hc k
  have hs : IsPullback (a.inv ≫ pullback.fst q j[k]) (pullback.snd (PL ↘ S) s[k]) q j[k] := by
    have he : a.hom ≫ pullback.snd (PL ↘ S) s[k] = pullback.snd q j[k] :=
      hirzebruchRulingAffineIso_hom_snd b e r hr hΦ hc k
    exact (IsPullback.of_hasPullback q j[k]).of_iso' a.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp [← he])
      (by simp) (by simp)
  have hpull : IsPullback (pullback.fst (PL ↘ S) (p ≫ PL ↘ S)) (pullback.snd _ _)
      (PL ↘ S) (l ≫ s[k]) :=
    hj ▸ IsPullback.of_hasPullback (PL ↘ S) (l ≫ s[k])
  have hw := hpull.of_right' (IsPullback.of_hasPullback (PL ↘ S) s[k])
  exact ⟨_, hl ▸ hw.paste_horiz hs⟩

include hΦ hc in
/-- The native scheme-theoretic fiber is a projective line over the point's residue field. -/
theorem exists_hirzebruch_fiber_iso_projectiveLine (y : PL) :
    ∃ a : projectiveLine (Scheme.residueField PL y) ≅ Scheme.Hom.fiber q y,
      a.hom ≫ Scheme.Hom.fiberToSpecResidueField q y = projectiveLine (Scheme.residueField PL y) ↘
        Spec (CommRingCat.of (Scheme.residueField PL y)) := by
  unfold Scheme.Hom.fiber Scheme.Hom.fiberToSpecResidueField
  let p := Scheme.fromSpecResidueField PL y
  obtain ⟨k, x, hx⟩ := exists_projectiveLineAffineFanι_apply_eq y
  have hp : Set.range p ⊆ Set.range j[k] := by
    rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff]
    exact ⟨x, hx⟩
  obtain ⟨u, hu⟩ := exists_isPullback_hirzebruch_ruling_of_range b e hΦ hc r hr p k hp
  let : Algebra ℂ (Scheme.residueField PL y) := (Spec.preimage (p ≫ PL ↘ S)).hom.toAlgebra
  have hp' : Spec.map (CommRingCat.ofHom (algebraMap ℂ (Scheme.residueField PL y))) = p ≫ PL ↘ S :=
    Spec.map_preimage _
  have hbase := projectiveLine.isPullback_baseChangeProjection ℂ (Scheme.residueField PL y)
  rw [hp'] at hbase
  exact ⟨hbase.isoPullback ≪≫ hu.isoPullback, by
    rw [Iso.trans_hom, Category.assoc,
      hu.isoPullback_hom_snd, hbase.isoPullback_hom_snd]⟩

include hΦ hc in
private theorem exists_isPullback_hirzebruch_closedFiber (y : PL)
    (hy : IsClosed ({y} : Set PL)) :
    ∃ u : PL ⟶ X, IsPullback u (PL ↘ S) q (pointOfClosedPoint (PL ↘ S) y hy) := by
  let p := pointOfClosedPoint (PL ↘ S) y hy
  have hp : p ≫ PL ↘ S = 𝟙 S := pointOfClosedPoint_comp _ y hy
  obtain ⟨k, x, hx⟩ := exists_projectiveLineAffineFanι_apply_eq y
  have hrange : Set.range p ⊆ Set.range j[k] := Set.range_subset_iff.mpr fun a ↦
    ⟨x, hx.trans (pointOfClosedPoint_apply (PL ↘ S) y hy a).symm⟩
  obtain ⟨u, hu⟩ := exists_isPullback_hirzebruch_ruling_of_range b e hΦ hc r hr p k hrange
  have htriv : IsPullback (𝟙 PL) (PL ↘ S) (PL ↘ S) (p ≫ PL ↘ S) := by
    rw [hp]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨htriv.isoPullback.hom ≫ u, hu.of_iso' htriv.isoPullback (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by rfl)⟩

open LineBundleClass Scheme.IdealSheafData in
include hΦ hc in
/-- In Hirzebruch Picard coordinates the degree on any closed fiber is the
coefficient of the section class. The fiber isomorphism is over the ground field. -/
theorem exists_hirzebruch_fiber_iso_with_degree (y : PL) (hy : IsClosed ({y} : Set PL)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    ∃ a : PL ≅ Scheme.Hom.fiber q y,
      a.hom ≫ Scheme.Hom.fiberι q y ≫ X ↘ S = PL ↘ S ∧
      ∀ L : LineBundleClass X,
        intersectionNumber ℂ (a.hom ≫ Scheme.Hom.fiberι q y) L =
          (Φ.hirzebruchPicardBasis b e hΦ r hr).repr (Additive.ofMul L) 1 := by
  intro hcone
  let := hcone
  unfold Scheme.Hom.fiber Scheme.Hom.fiberι
  let p := pointOfClosedPoint (PL ↘ S) y hy
  have hp : p ≫ PL ↘ S = 𝟙 S := pointOfClosedPoint_comp _ y hy
  obtain ⟨u, hu⟩ := exists_isPullback_hirzebruch_closedFiber b e hΦ hc r hr y hy
  let z := asIso (Spec.map (residueFieldIsoBase (PL ↘ S) y hy).hom)
  have hz : z.hom ≫ Scheme.fromSpecResidueField PL y = p := rfl
  have hf : IsPullback u ((PL ↘ S) ≫ z.hom) q (Scheme.fromSpecResidueField PL y) :=
    hu.of_iso (Iso.refl _) (Iso.refl _) z (Iso.refl _) (by simp) (by simp) (by simp)
      (by simpa using hz.symm)
  have hover : u ≫ X ↘ S = PL ↘ S := by
    rw [← comp_over q S, hu.w_assoc, pointOfClosedPoint_comp, Category.comp_id]
  let : u.IsOver S := ⟨hover⟩
  let : IsClosedImmersion p := p.isClosedImmersion_of_comp_eq_id hp
  let : IsClosedImmersion u := MorphismProperty.of_isPullback hu.flip inferInstance
  let : (Φ.algebraicRealization).IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
    (Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let d := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  obtain ⟨hI, hclass⟩ := Φ.toLineBundleClass_hirzebruch_characterRuling_fiber b e hΦ r hr p hp
  have hFC := congrArg Additive.toMul hclass
  simp only [toMul_ofMul] at hFC
  have hker := ker_eq_comap_of_isPullback p hu
  let hD := hker ▸ hI
  refine ⟨hf.isoPullback, ?_, ?_⟩
  · rw [← Category.assoc, hf.isoPullback_hom_fst, hover]
  · intro L
    rw [hf.isoPullback_hom_fst,
      ← Chow.classIntersectionNumber_eq_intersectionNumber_of_isEffectiveCartier_ker ℂ d.le u
        (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ) hD,
      mk_toInvertibleSheaf_congr _ hI hker, hFC]
    simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using
      (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc (Additive.ofMul L)).1

open LineBundleClass Scheme.IdealSheafData in
include hΦ hc in
/-- The line bundle of the invariant section at ray `r 0` has degree one on
every closed fiber of the Hirzebruch ruling. -/
theorem exists_hirzebruch_polarized_projectiveLine_fibers :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let L := (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ (r 0)).toInvertibleSheaf.dual
    ∀ y : PL, IsClosed ({y} : Set PL) →
      ∃ a : PL ≅ Scheme.Hom.fiber q y,
        a.hom ≫ Scheme.Hom.fiberι q y ≫ X ↘ S = PL ↘ S ∧
        intersectionNumber ℂ (a.hom ≫ Scheme.Hom.fiberι q y) (LineBundleClass.mk L) = 1 := by
  classical
  intro hcone L y hy
  let := hcone
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  obtain ⟨a, hover, hdeg⟩ := exists_hirzebruch_fiber_iso_with_degree b e hΦ hc r hr y hy
  have hL : (Φ.hirzebruchPicardBasis b e hΦ r hr) 1 = Additive.ofMul (LineBundleClass.mk L) := by
    rw [hirzebruchPicardBasis_apply_one, rayDivisorToPicard_single, one_zsmul,
      primeDivisorClass_def,
      mk_toInvertibleSheaf_congr _ _ (Φ.rayBoundaryIdeal_def hΦ (r 0)).symm, inv_mk]
  refine ⟨a, hover, ?_⟩
  rw [hdeg, ← hL, Basis.repr_self]
  simp

end TauCeti.Toric.Fan
