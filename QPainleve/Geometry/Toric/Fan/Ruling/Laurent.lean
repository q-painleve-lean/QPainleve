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

open AlgebraicGeometry CategoryTheory Limits LaurentPolynomial Module Multiplicative PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

variable (K : Type) [CommRing K]

local notation "L" => LaurentPolynomial K
local notation "T₀" => projectiveLineTorusFan.finiteFanScheme K
local notation "base" => Spec (CommRingCat.of K)
local notation "S" => Spec (CommRingCat.of L)
local notation "chart" => projectiveLine.polynomialChartι K 0
local notation "loc" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) L))

private instance : IsOpenImmersion (loc) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial K)

private theorem range_laurentSpecMap_comp_polynomialChartι :
    Set.range ((loc) ≫ chart) = Set.range (projectiveLineTorusι K) := by
  rw [range_projectiveLineTorusι K, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hr : Set.range (loc) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) : Set (PrimeSpectrum _)) := by
    -- The map of spectrum points is the comap of prime ideals under localization.
    change Set.range (PrimeSpectrum.comap (algebraMap (Polynomial K) L)) = _
    exact PrimeSpectrum.localization_away_comap_range L (Polynomial.X : Polynomial K)
  have hrev := projectiveLine.polynomialChartι_preimage_basicOpen_rev K 0
  have hpre : chart ⁻¹' Set.range (projectiveLine.polynomialChartι K 1) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) : Set (PrimeSpectrum _)) := by
    rw [← Scheme.Hom.coe_opensRange, projectiveLine.opensRange_polynomialChartι,
      ← Scheme.Hom.coe_preimage]
    exact congrArg SetLike.coe hrev
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The torus of the projective line in the Laurent coordinate `X₁ / X₀`. -/
def projectiveLineTorusIsoSpecLaurent : T₀ ≅ S :=
  IsOpenImmersion.isoOfRangeEq (projectiveLineTorusι K) ((loc) ≫ chart)
    (range_laurentSpecMap_comp_polynomialChartι K).symm

/-- The Laurent chart gives the original inclusion of the projective-line torus. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusIsoSpecLaurent_hom_comp_chart :
    (projectiveLineTorusIsoSpecLaurent K).hom ≫ (loc) ≫ chart = projectiveLineTorusι K := by
  unfold projectiveLineTorusIsoSpecLaurent
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The Laurent chart respects the structure morphism to the coefficient ring. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusIsoSpecLaurent_hom_comp_toBase :
    (projectiveLineTorusIsoSpecLaurent K).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      T₀ ↘ base := by
  have hloc : (loc) ≫ chart ≫ (projectiveLine K ↘ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [projectiveLine.polynomialChartι_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro z
    simp
  rw [← hloc, projectiveLineTorusIsoSpecLaurent_hom_comp_chart_assoc, CategoryTheory.comp_over]

/-- The point `[1 : a]` of the base torus is Laurent evaluation at `a`. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPoint_comp_projectiveLineTorusIsoSpecLaurent (a : Kˣ) :
    projectiveLineTorusPoint K a ≫ (projectiveLineTorusIsoSpecLaurent K).hom =
      Spec.map (CommRingCat.ofHom (laurentEval a : L →ₐ[K] K).toRingHom) := by
  apply (cancel_mono ((loc) ≫ chart)).mp
  rw [Category.assoc, projectiveLineTorusIsoSpecLaurent_hom_comp_chart,
    projectiveLineTorusPoint_comp_projectiveLineTorusι, projectiveLine.polynomialPoint_def,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have he : (laurentEval a : L →ₐ[K] K).comp Polynomial.toLaurentAlg =
      Polynomial.aeval (a : K) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X,
      laurentEval_T_one, Polynomial.aeval_X]
  have he' : (laurentEval a : L →ₐ[K] K).toRingHom.comp (algebraMap (Polynomial K) L) =
      Polynomial.eval₂RingHom (RingHom.id K) (a : K) :=
    congrArg AlgHom.toRingHom he
  rw [he']

namespace Fan

local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "F" => Fan.prod P projectiveLineTorusFan
local notation "π₁" => (FanHom.finiteFanSchemeHom K (FanHom.fst P projectiveLineTorusFan) ≫
  Iso.hom (Fan.projectiveLineToricIso K))
local notation "π₂" => FanHom.finiteFanSchemeHom K (FanHom.snd P projectiveLineTorusFan)

private theorem isPullback_laurentProduct :
    IsPullback π₁ (π₂ ≫ (projectiveLineTorusIsoSpecLaurent K).hom)
      (projectiveLine K ↘ base) (Spec.algebraMap K L) := by
  refine (isPullback_projectiveLineTorusProduct K).of_iso'
    (Iso.refl _) (Iso.refl _) (projectiveLineTorusIsoSpecLaurent K).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Spec.algebraMap,
      ← projectiveLineTorusIsoSpecLaurent_hom_comp_toBase, Iso.inv_hom_id_assoc]

/-- The product fan of the projective line and its base torus realizes the
projective line over the Laurent polynomial ring. -/
def projectiveLineTorusProductIsoLaurent : (F).finiteFanScheme K ≅ projectiveLine L :=
  (isPullback_laurentProduct K).isoPullback ≪≫
    (projectiveLine.isPullback_baseChangeProjection K L).isoPullback.symm

/-- The Laurent model's fiber projection is the first fan projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusProductIsoLaurent_hom_baseChangeProjection :
    (projectiveLineTorusProductIsoLaurent K).hom ≫ projectiveLine.baseChangeProjection K L =
      π₁ := by
  simp [projectiveLineTorusProductIsoLaurent]

/-- The Laurent model's structural map is the second fan projection, expressed
in the Laurent coordinate of the base. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusProductIsoLaurent_hom_toBase :
    (projectiveLineTorusProductIsoLaurent K).hom ≫ (projectiveLine L ↘ S) =
      π₂ ≫ (projectiveLineTorusIsoSpecLaurent K).hom := by
  simp [projectiveLineTorusProductIsoLaurent]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (b : Basis (Fin 2) ℤ N) (hm : m = (b.coord 1).toAddMonoidHom)
  (hpos : hull ℝ {i (b 0)} ∈ Φ.cones) (hneg : hull ℝ {-i (b 0)} ∈ Φ.cones)

private theorem isPullback_projectiveLineLaurent :
    IsPullback (projectiveLine.baseChangeProjection K L)
      ((projectiveLine L ↘ S) ≫ (projectiveLineTorusIsoSpecLaurent K).inv)
      (projectiveLine K ↘ base) (T₀ ↘ base) := by
  apply (projectiveLine.isPullback_baseChangeProjection K L).of_iso
    (Iso.refl _) (Iso.refl _) (projectiveLineTorusIsoSpecLaurent K).symm (Iso.refl _)
  · simp
  · simp
  · simp
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id,
      ← projectiveLineTorusIsoSpecLaurent_hom_comp_toBase, Iso.inv_hom_id_assoc]

/-- The ruling over the base torus in adapted coordinates, as a projective line
over the Laurent polynomial ring. -/
def characterRulingLaurentIso :
    pullback (Φ.characterRuling K m h) (projectiveLineTorusι K) ≅ projectiveLine L :=
  Φ.characterRulingTorusIso K m h b hm hpos hneg ≪≫
    (isPullback_projectiveLineLaurent K).isoPullback.symm

/-- The Laurent comparison preserves the first coordinate of the ruling product. -/
@[reassoc (attr := simp)]
theorem characterRulingLaurentIso_hom_comp_baseChangeProjection :
    (Φ.characterRulingLaurentIso K m h b hm hpos hneg).hom ≫
        projectiveLine.baseChangeProjection K L =
      (Φ.characterRulingTorusIso K m h b hm hpos hneg).hom ≫ pullback.fst _ _ := by
  rw [characterRulingLaurentIso, Iso.trans_hom, Category.assoc,
    Iso.symm_hom, IsPullback.isoPullback_inv_fst]

/-- The Laurent comparison sends the ruling's second coordinate to the base torus
in its Laurent coordinate. -/
@[reassoc (attr := simp)]
theorem characterRulingLaurentIso_hom_comp_toBase :
    (Φ.characterRulingLaurentIso K m h b hm hpos hneg).hom ≫ (projectiveLine L ↘ S) =
      pullback.snd (Φ.characterRuling K m h) (projectiveLineTorusι K) ≫
        (projectiveLineTorusIsoSpecLaurent K).hom := by
  have hproj := (isPullback_projectiveLineLaurent K).isoPullback_inv_snd
  rw [← cancel_mono (projectiveLineTorusIsoSpecLaurent K).inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    characterRulingLaurentIso, Iso.trans_hom, Category.assoc, Iso.symm_hom, hproj,
    Φ.characterRulingTorusIso_hom_snd K]

/-- The coordinate-ring projection of the Laurent product, followed by the Laurent chart
of the base, is the original ruling. -/
@[reassoc]
theorem characterRulingLaurentIso_hom_comp_toRuling :
    (Φ.characterRulingLaurentIso K m h b hm hpos hneg).hom ≫ (projectiveLine L ↘ S) ≫
        (loc) ≫ chart =
      pullback.fst (Φ.characterRuling K m h) (projectiveLineTorusι K) ≫
        Φ.characterRuling K m h := by
  rw [Φ.characterRulingLaurentIso_hom_comp_toBase_assoc K,
    projectiveLineTorusIsoSpecLaurent_hom_comp_chart, pullback.condition]

local notation "eL" => Φ.characterRulingLaurentIso K m h b hm hpos hneg
local notation "G" => AddMonoidAlgebra K (N →+ ℤ)
local notation "g" =>
  AddMonoidAlgebra.mapDomainAlgHom K K (AddSubmonoid.subtype (dualSemigroup (lattice Φ) ⊥))
local notation "aG" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g))
local notation "k" => laurentEval (MonoidHom.toHomUnits (AddMonoidAlgebra.of K (N →+ ℤ)) (ofAdd m))

private theorem additiveDenseTorus_comp_polynomialPoint (a : N →+ ℤ) :
    aG ≫ projectiveLine.polynomialPoint K (algebraMap K _) 0
        (AddMonoidAlgebra.single (⟨a, by simp⟩ : dualSemigroup Φ.lattice ⊥) 1) =
      projectiveLine.polynomialPoint K (algebraMap K G) 0 (AddMonoidAlgebra.single a 1) := by
  rw [projectiveLine.SpecMap_polynomialPoint]
  congr 1
  · exact RingHom.ext (g).commutes
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    rfl

private theorem additiveDenseTorus_comp_baseChangeProjection (h₀ : Nonempty Φ.cones) :
    aG ≫ Φ.denseTorusιRulingTorus K m h h₀ ≫ (eL).hom ≫
        projectiveLine.baseChangeProjection K L =
      projectiveLine.polynomialPoint K (algebraMap K G) 0
        (AddMonoidAlgebra.single (b.coord 0).toAddMonoidHom 1) := by
  rw [Φ.characterRulingLaurentIso_hom_comp_baseChangeProjection K,
    denseTorusιRulingTorus_def, Category.assoc]
  let U := Φ.characterRulingTorusSubfan m h
  let σ : U.cones := ⟨⊥, Φ.bot_mem_characterRulingTorusSubfan m h h₀⟩
  have hχ : (if (0 : Fin 2) = 0 then (b.coord 0).toAddMonoidHom else
      -(b.coord 0).toAddMonoidHom) ∈ dualSemigroup U.lattice σ.val := by simp [σ]
  rw [Φ.affineToricChartι_comp_characterRulingTorusIso_fst K m h b hm hpos hneg σ 0 hχ]
  simpa [σ] using
    additiveDenseTorus_comp_polynomialPoint K (Φ := U) (b.coord 0).toAddMonoidHom

private theorem additiveDenseTorus_comp_laurentBase (h₀ : Nonempty Φ.cones) :
    aG ≫ Φ.denseTorusιRulingTorus K m h h₀ ≫ (eL).hom ≫ (projectiveLine L ↘ Spec (.of L)) =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom k)) := by
  apply (cancel_mono ((loc) ≫ chart)).mp
  simp only [Category.assoc, Φ.characterRulingLaurentIso_hom_comp_toBase_assoc K]
  rw [projectiveLineTorusIsoSpecLaurent_hom_comp_chart, ← pullback.condition,
    denseTorusιRulingTorus_fst_assoc, Φ.denseTorusι_comp_characterRuling K m h h₀,
    additiveDenseTorus_comp_polynomialPoint K (Φ := Φ), ← projectiveLine.polynomialPoint_X,
    projectiveLine.SpecMap_polynomialPoint, projectiveLine.SpecMap_polynomialPoint]
  simp only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
  congr 1
  · ext a
    simp
  · simp [MonoidHom.coe_toHomUnits, AddMonoidAlgebra.of_apply]

/-- On the dense torus, the Laurent product coordinates are the two characters dual
to the adapted integral basis. The fiber coordinate is in the chart at section zero. -/
@[reassoc]
theorem additiveDenseTorus_comp_characterRulingLaurentIso (h₀ : Nonempty Φ.cones) :
    aG ≫ Φ.denseTorusιRulingTorus K m h h₀ ≫ (eL).hom =
      projectiveLine.polynomialPoint L (AlgHom.toRingHom k) 0
        (AddMonoidAlgebra.single (b.coord 0).toAddMonoidHom 1) := by
  apply (projectiveLine.isPullback_baseChangeProjection K L).hom_ext
  · rw [Category.assoc, Category.assoc,
      additiveDenseTorus_comp_baseChangeProjection K Φ m h b hm hpos hneg,
      projectiveLine.polynomialPoint_comp_baseChangeProjection]
    simp
  · rw [Category.assoc, Category.assoc,
      additiveDenseTorus_comp_laurentBase K Φ m h b hm hpos hneg,
      projectiveLine.polynomialPoint_over]

end Fan

end TauCeti.Toric
