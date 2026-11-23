/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Torus
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# Laurent coordinates on the base of a toric ruling

The dense torus of the projective line is the spectrum of the Laurent polynomial ring,
with coordinate the ratio of the second homogeneous coordinate to the first. Thus the
product neighborhood of a toric ruling can be written as a projective line over this
Laurent ring, with its nonzero fibers specified by Laurent evaluation.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits LaurentPolynomial Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

local notation "L" => LaurentPolynomial ℂ
local notation "T₀" => projectiveLineTorusFan.algebraicRealization
local notation "base" => Spec (CommRingCat.of ℂ)
local notation "S" => Spec (CommRingCat.of L)
local notation "chart" => projectiveLine.polynomialChartι ℂ 0
local notation "loc" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℂ) L))

private instance : IsOpenImmersion (loc) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial ℂ)

private theorem range_laurentSpecMap_comp_polynomialChartι :
    Set.range ((loc) ≫ chart) = Set.range projectiveLineTorusι := by
  rw [range_projectiveLineTorusι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hr : Set.range (loc) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℂ) : Set (PrimeSpectrum _)) := by
    -- The map of spectrum points is the comap of prime ideals under localization.
    change Set.range (PrimeSpectrum.comap (algebraMap (Polynomial ℂ) L)) = _
    exact PrimeSpectrum.localization_away_comap_range L (Polynomial.X : Polynomial ℂ)
  have hrev := projectiveLine.polynomialChartι_preimage_basicOpen_rev ℂ 0
  have hpre : chart ⁻¹' Set.range (projectiveLine.polynomialChartι ℂ 1) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℂ) : Set (PrimeSpectrum _)) := by
    rw [← Scheme.Hom.coe_opensRange, projectiveLine.opensRange_polynomialChartι,
      ← Scheme.Hom.coe_preimage]
    exact congrArg SetLike.coe hrev
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The torus of the projective line in the Laurent coordinate `X₁ / X₀`. -/
def projectiveLineTorusIsoSpecLaurent : T₀ ≅ S :=
  IsOpenImmersion.isoOfRangeEq projectiveLineTorusι ((loc) ≫ chart)
    range_laurentSpecMap_comp_polynomialChartι.symm

/-- The Laurent chart gives the original inclusion of the projective-line torus. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusIsoSpecLaurent_hom_comp_chart :
    projectiveLineTorusIsoSpecLaurent.hom ≫ (loc) ≫ chart = projectiveLineTorusι := by
  unfold projectiveLineTorusIsoSpecLaurent
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The Laurent chart respects the complex structure morphism. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusIsoSpecLaurent_hom_comp_toBase :
    projectiveLineTorusIsoSpecLaurent.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) =
      T₀ ↘ base := by
  have hloc : (loc) ≫ chart ≫ (projectiveLine ℂ ↘ base) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
    rw [projectiveLine.polynomialChartι_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro z
    simp
  rw [← hloc, projectiveLineTorusIsoSpecLaurent_hom_comp_chart_assoc, CategoryTheory.comp_over]

/-- The point `[1 : a]` of the base torus is Laurent evaluation at `a`. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPoint_comp_projectiveLineTorusIsoSpecLaurent (a : ℂˣ) :
    projectiveLineTorusPoint a ≫ projectiveLineTorusIsoSpecLaurent.hom =
      Spec.map (CommRingCat.ofHom (laurentEval a : L →ₐ[ℂ] ℂ).toRingHom) := by
  apply (cancel_mono ((loc) ≫ chart)).mp
  rw [Category.assoc, projectiveLineTorusIsoSpecLaurent_hom_comp_chart,
    projectiveLineTorusPoint_comp_projectiveLineTorusι, projectiveLine.polynomialPoint_def,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have he : (laurentEval a : L →ₐ[ℂ] ℂ).comp Polynomial.toLaurentAlg =
      Polynomial.aeval (a : ℂ) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X,
      laurentEval_T_one, Polynomial.aeval_X]
  have he' : (laurentEval a : L →ₐ[ℂ] ℂ).toRingHom.comp (algebraMap (Polynomial ℂ) L) =
      Polynomial.eval₂RingHom (RingHom.id ℂ) (a : ℂ) :=
    congrArg AlgHom.toRingHom he
  rw [he']

namespace Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom)
  (hpos : hull ℝ {i (b 0)} ∈ Φ.cones) (hneg : hull ℝ {-i (b 0)} ∈ Φ.cones)

private theorem isPullback_projectiveLineLaurent :
    IsPullback (projectiveLine.baseChangeProjection ℂ L)
      ((projectiveLine L ↘ S) ≫ projectiveLineTorusIsoSpecLaurent.inv)
      (projectiveLine ℂ ↘ base) (T₀ ↘ base) := by
  apply (projectiveLine.isPullback_baseChangeProjection ℂ L).of_iso
    (Iso.refl _) (Iso.refl _) projectiveLineTorusIsoSpecLaurent.symm (Iso.refl _)
  · simp
  · simp
  · simp
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      ← projectiveLineTorusIsoSpecLaurent_hom_comp_toBase, Iso.inv_hom_id_assoc]

/-- The ruling over the base torus in adapted coordinates, as a projective line
over the Laurent polynomial ring. -/
def characterRulingLaurentIso :
    pullback (Φ.characterRuling m h) projectiveLineTorusι ≅ projectiveLine L :=
  Φ.characterRulingTorusIso m h b hm hpos hneg ≪≫ isPullback_projectiveLineLaurent.isoPullback.symm

/-- The Laurent comparison preserves the first coordinate of the ruling product. -/
@[reassoc (attr := simp)]
theorem characterRulingLaurentIso_hom_comp_baseChangeProjection :
    (Φ.characterRulingLaurentIso m h b hm hpos hneg).hom ≫
        projectiveLine.baseChangeProjection ℂ L =
      (Φ.characterRulingTorusIso m h b hm hpos hneg).hom ≫ pullback.fst _ _ := by
  rw [characterRulingLaurentIso, Iso.trans_hom, Category.assoc,
    Iso.symm_hom, IsPullback.isoPullback_inv_fst]

/-- The Laurent comparison sends the ruling's second coordinate to the base torus
in its Laurent coordinate. -/
@[reassoc (attr := simp)]
theorem characterRulingLaurentIso_hom_comp_toBase :
    (Φ.characterRulingLaurentIso m h b hm hpos hneg).hom ≫ (projectiveLine L ↘ S) =
      pullback.snd (Φ.characterRuling m h) projectiveLineTorusι ≫
        projectiveLineTorusIsoSpecLaurent.hom := by
  have hproj := isPullback_projectiveLineLaurent.isoPullback_inv_snd
  rw [← cancel_mono projectiveLineTorusIsoSpecLaurent.inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    characterRulingLaurentIso, Iso.trans_hom, Category.assoc, Iso.symm_hom, hproj,
    Φ.characterRulingTorusIso_hom_snd]

end Fan

end TauCeti.Toric
