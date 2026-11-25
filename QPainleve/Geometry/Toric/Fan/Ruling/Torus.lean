/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.AffineChart
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic

import QPainleve.LinearAlgebra.Dual.Basis
import QPainleve.Geometry.Toric.Fan.DenseTorus
import QPainleve.Geometry.Toric.Fan.Scheme
import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Isomorphism
import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# The torus neighborhood of a character ruling

If a rank-two fan contains both rays in the kernel of a primitive character, the restriction
of the associated ruling over the dense torus of the projective line is a product. The
primitive ray and a choice of complementary lattice vector specify its trivialization.

This is the neighborhood of the nonzero fibers used for elementary transformations in
Gross, Hacking and Keel, *Birational geometry of cluster algebras*, §3.1. The comparison
uses Tau Ceti's pullback square for open subfans and its product-fan isomorphism.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

local notation "P" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
local notation "S₀" => ({⊥} : Set (PointedCone ℝ (Fin 1 → ℝ)))
local notation "base" => Spec (CommRingCat.of ℂ)

private theorem zeroCone_subset_projectiveLine : S₀ ⊆ (P).cones := by
  rintro σ (rfl : σ = ⊥)
  exact Fan.bot_mem_projectiveSpace_cones _ _

private theorem zeroCone_closedUnderFaces ⦃σ τ : PointedCone ℝ (Fin 1 → ℝ)⦄
    (hσ : σ ∈ S₀) (hτ : τ.IsFaceOf σ) : τ ∈ S₀ := by
  rw [Set.mem_singleton_iff] at hσ ⊢
  exact le_bot_iff.mp (hσ ▸ hτ.le)

/-- The open subfan of the projective line consisting of the zero cone. -/
def projectiveLineTorusFan : Fan ((Int.castAddHom ℝ).compLeft (Fin 1)) :=
  (P).subfan S₀ zeroCone_subset_projectiveLine zeroCone_closedUnderFaces

@[simp] theorem mem_projectiveLineTorusFan_cones {σ : PointedCone ℝ (Fin 1 → ℝ)} :
    σ ∈ projectiveLineTorusFan.cones ↔ σ = ⊥ := by
  rw [projectiveLineTorusFan, Fan.subfan_cones, Set.mem_singleton_iff]

/-- The zero-cone subfan included in the fan of the projective line. -/
def projectiveLineTorusFanInclusion : FanHom projectiveLineTorusFan P :=
  (P).subfanInclusion S₀ zeroCone_subset_projectiveLine zeroCone_closedUnderFaces

/-- The inclusion of the zero-cone subfan is the identity on its lattice. -/
@[simp]
theorem projectiveLineTorusFanInclusion_latticeMap :
    projectiveLineTorusFanInclusion.latticeMap = AddMonoidHom.id (Fin 1 → ℤ) := by
  rw [projectiveLineTorusFanInclusion, Fan.subfanInclusion_latticeMap]

/-- The inclusion of the dense torus of the projective line, with homogeneous coordinates
numbered by `Fin 2`. -/
def projectiveLineTorusι : projectiveLineTorusFan.algebraicRealization ⟶ projectiveLine ℂ :=
  projectiveLineTorusFanInclusion.algebraicMap ≫ Fan.projectiveLineToricIso.hom

/-- The base torus immersion is the realization of the zero-cone inclusion. -/
theorem projectiveLineTorusι_def :
    projectiveLineTorusι =
      projectiveLineTorusFanInclusion.algebraicMap ≫ Fan.projectiveLineToricIso.hom :=
  (rfl)

instance : IsOpenImmersion projectiveLineTorusι := by
  rw [projectiveLineTorusι]
  let : IsOpenImmersion projectiveLineTorusFanInclusion.algebraicMap :=
    Fan.isOpenImmersion_subfanInclusion_algebraicMap P S₀ zeroCone_subset_projectiveLine
      zeroCone_closedUnderFaces
  infer_instance

instance : projectiveLineTorusι.IsOver base where
  comp_over := by
    rw [projectiveLineTorusι, CategoryTheory.comp_over]

/-- The torus of the projective line is the overlap of its two polynomial charts. -/
theorem range_projectiveLineTorusι :
    Set.range projectiveLineTorusι = Set.range (projectiveLine.polynomialChartι ℂ 0) ∩
      Set.range (projectiveLine.polynomialChartι ℂ 1) := by
  have h₀ : Nonempty (P).cones := ⟨⟨⊥, zeroCone_subset_projectiveLine (Set.mem_singleton _)⟩⟩
  have hr : Set.range projectiveLineTorusFanInclusion.algebraicMap =
      Set.range ((P).denseTorusι h₀) :=
    (P).range_subfanInclusion_algebraicMap_of_eq_singleton_bot h₀ zeroCone_subset_projectiveLine
      zeroCone_closedUnderFaces rfl
  rw [projectiveLineTorusι, ← Fan.range_denseTorusι_comp_projectiveLineToricIso h₀]
  -- Both composites apply the same projective comparison to the image of the zero-cone chart.
  change Set.range (Fan.projectiveLineToricIso.hom ∘ projectiveLineTorusFanInclusion.algebraicMap) =
    Set.range (Fan.projectiveLineToricIso.hom ∘ (P).denseTorusι h₀)
  rw [Set.range_comp, Set.range_comp, hr]

/-- The point `[1 : a]` lies in the torus for each nonzero scalar `a`. -/
private theorem range_polynomialPoint_subset_projectiveLineTorusι (a : ℂˣ) :
    Set.range (projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (a : ℂ)) ⊆
      Set.range projectiveLineTorusι := by
  rw [range_projectiveLineTorusι, projectiveLine.polynomialPoint_def]
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply]
  refine ⟨⟨_, rfl⟩, ?_⟩
  have hrev : (0 : Fin 2).rev = 1 := by decide
  have hpre := projectiveLine.polynomialChartι_preimage_basicOpen_rev ℂ 0
  rw [hrev] at hpre
  rw [← Scheme.Hom.coe_opensRange, projectiveLine.opensRange_polynomialChartι,
    SetLike.mem_coe, ← Scheme.Hom.mem_preimage, hpre]
  let q := Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id ℂ) (a : ℂ)))
  have hX : q ⁻¹ᵁ PrimeSpectrum.basicOpen Polynomial.X = PrimeSpectrum.basicOpen (a : ℂ) := by
    dsimp only [q]
    rw [SpecMap_preimage_basicOpen]
    exact congrArg (fun z : ℂ ↦ PrimeSpectrum.basicOpen z) (Polynomial.eval₂_X _ _)
  apply (Scheme.Hom.mem_preimage q).mp
  rw [hX]
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun ha ↦
    x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem ha a.isUnit)

/-- The torus point whose affine projective-line coordinate is `a`. -/
def projectiveLineTorusPoint (a : ℂˣ) : base ⟶ projectiveLineTorusFan.algebraicRealization :=
  IsOpenImmersion.lift projectiveLineTorusι
    (projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (a : ℂ))
    (range_polynomialPoint_subset_projectiveLineTorusι a)

/-- The lift to the torus maps to the projective point `[1 : a]`. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPoint_comp_projectiveLineTorusι (a : ℂˣ) :
    projectiveLineTorusPoint a ≫ projectiveLineTorusι =
      projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (a : ℂ) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The torus point is a section over the coefficient field. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPoint_comp_over (a : ℂˣ) :
    projectiveLineTorusPoint a ≫ (projectiveLineTorusFan.algebraicRealization ↘ base) = 𝟙 base := by
  rw [← CategoryTheory.comp_over projectiveLineTorusι, ← Category.assoc,
    projectiveLineTorusPoint_comp_projectiveLineTorusι, projectiveLine.polynomialPoint_over]
  exact Spec.map_id _

namespace Fan

/-- The zero-cone fan included in either affine chart of the projective line. -/
def projectiveLineTorusToAffineFan (k : Fin 2) :
    FanHom projectiveLineTorusFan (projectiveLineAffineFan k) :=
  FanHom.ofLatticeMap _ _ (AddMonoidHom.id (Fin 1 → ℤ)) fun σ hσ ↦ by
    obtain rfl := mem_projectiveLineTorusFan_cones.mp hσ
    exact ⟨⊥, (projectiveLineAffineFan k).bot_mem
      (mem_projectiveLineAffineFan_cones.mpr (.refl _)), by simp⟩

/-- Including the base torus in an affine chart leaves the lattice unchanged. -/
@[simp]
theorem projectiveLineTorusToAffineFan_latticeMap (k : Fin 2) :
    (projectiveLineTorusToAffineFan k).latticeMap = AddMonoidHom.id (Fin 1 → ℤ) := by
  rw [projectiveLineTorusToAffineFan, FanHom.ofLatticeMap_latticeMap]

/-- Either inclusion of the overlap recovers the base torus immersion. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusToAffineFan_algebraicMap_comp_ι (k : Fin 2) :
    (projectiveLineTorusToAffineFan k).algebraicMap ≫ projectiveLineAffineFanι k =
      projectiveLineTorusι := by
  rw [projectiveLineAffineFanι_def, ← Category.assoc, ← FanHom.algebraicMap_comp,
    projectiveLineTorusι]
  congr 2
  apply FanHom.ext
  simp

/-- The product fan over the projective-line torus realizes the scheme-theoretic
product of the projective line and the torus. -/
theorem isPullback_projectiveLineTorusProduct :
    IsPullback ((FanHom.fst P projectiveLineTorusFan).algebraicMap ≫ projectiveLineToricIso.hom)
      (FanHom.snd P projectiveLineTorusFan).algebraicMap (projectiveLine ℂ ↘ base)
      (projectiveLineTorusFan.algebraicRealization ↘ base) := by
  refine ((P).isPullback_fst_snd_algebraicMap projectiveLineTorusFan).of_iso'
    (Iso.refl _) projectiveLineToricIso.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      ← cancel_epi projectiveLineToricIso.hom, Iso.hom_inv_id_assoc,
      ← Fan.algebraicRealization_over, CategoryTheory.comp_over]
  · simp [Fan.algebraicRealization_over]

section

local notation "p" => (projectiveLine ℂ ↘ base)
local notation "s[" k "]" => Fan.algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "t" => (projectiveLineTorusFan.algebraicRealization ↘ base)
local notation "a[" k "]" => FanHom.algebraicMap (projectiveLineTorusToAffineFan k)

/-- The map from the product over the base torus to the product over an affine chart
is the identity on the projective-line factor. -/
def projectiveLineTorusProductToAffine (k : Fin 2) : pullback p t ⟶ pullback p s[k] :=
  pullback.lift (pullback.fst p t) (pullback.snd p t ≫ a[k])
    (by rw [Category.assoc, FanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← Fan.algebraicRealization_over, pullback.condition])

local notation "d[" k "]" => projectiveLineTorusProductToAffine k

/-- The product inclusion preserves the fiber projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusProductToAffine_fst (k : Fin 2) :
    d[k] ≫ pullback.fst p s[k] = pullback.fst p t :=
  pullback.lift_fst _ _ _

/-- The product inclusion induces the torus inclusion on the base projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusProductToAffine_snd (k : Fin 2) :
    d[k] ≫ pullback.snd p s[k] = pullback.snd p t ≫ a[k] :=
  pullback.lift_snd _ _ _

/-- The product over the base torus is the preimage of that torus in either product chart. -/
theorem isPullback_projectiveLineTorusProductToAffine (k : Fin 2) :
    IsPullback d[k] (pullback.snd p t) (pullback.snd p s[k]) a[k] := by
  have h : a[k] ≫ s[k] = t :=
    (FanHom.algebraicMap_comp_algebraicRealizationStructureMap _).trans
      (Fan.algebraicRealization_over _).symm
  refine IsPullback.of_right ?_ (projectiveLineTorusProductToAffine_snd k)
    (IsPullback.of_hasPullback p s[k])
  simpa only [projectiveLineTorusProductToAffine_fst, h] using IsPullback.of_hasPullback p t

end

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)

local notation "f" => Φ.characterFanHom m h

/-- The open subfan above the dense torus of the ruling's projective-line target. -/
def characterRulingTorusSubfan : Fan i :=
  (f).preimageSubfan S₀ zeroCone_closedUnderFaces

local notation "U" => Φ.characterRulingTorusSubfan m h

/-- The inclusion of the open subfan above the dense torus into the whole fan. -/
def characterRulingTorusSubfanInclusion : FanHom U Φ :=
  Φ.subfanInclusion _ ((f).preimageCones_subset S₀)
    ((f).preimageCones_closedUnderFaces S₀ zeroCone_closedUnderFaces)

/-- Including the ruling's torus subfan leaves the lattice unchanged. -/
@[simp]
theorem characterRulingTorusSubfanInclusion_latticeMap :
    (Φ.characterRulingTorusSubfanInclusion m h).latticeMap = AddMonoidHom.id N :=
  subfanInclusion_latticeMap _ _ _ _

/-- The restriction of the character fan map to the two open subfans. -/
def characterRulingTorusFanHom : FanHom U projectiveLineTorusFan :=
  (f).restrictToPreimage S₀ zeroCone_subset_projectiveLine zeroCone_closedUnderFaces

@[simp] theorem characterRulingTorusFanHom_latticeMap (x : N) (j : Fin 1) :
    (Φ.characterRulingTorusFanHom m h).latticeMap x j = m x := by
  simp [characterRulingTorusFanHom]

/-- The toric scheme of the subfan above the dense torus is the base change of the ruling. -/
theorem isPullback_characterRulingTorusSubfan :
    IsPullback (Φ.characterRulingTorusSubfanInclusion m h).algebraicMap
      (Φ.characterRulingTorusFanHom m h).algebraicMap
      (Φ.characterRuling m h) projectiveLineTorusι := by
  have hbase : IsPullback projectiveLineTorusFanInclusion.algebraicMap (𝟙 _)
      projectiveLineToricIso.hom projectiveLineTorusι :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, projectiveLineTorusι]⟩
  have hpre : IsPullback (Φ.characterRulingTorusSubfanInclusion m h).algebraicMap
      (Φ.characterRulingTorusFanHom m h).algebraicMap (f).algebraicMap
      projectiveLineTorusFanInclusion.algebraicMap :=
    (f).isPullback_preimageSubfan_algebraicMap S₀ zeroCone_subset_projectiveLine
      zeroCone_closedUnderFaces
  simpa only [Category.comp_id, characterRuling_def] using hpre.paste_vert hbase

/-- A cone lies above the dense torus precisely when the ruling character vanishes on it. -/
theorem mem_characterRulingTorusSubfan_cones_iff {σ : PointedCone ℝ V} :
    σ ∈ (U).cones ↔ σ ∈ Φ.cones ∧ ∀ x ∈ σ, Φ.lattice.realCharacter m x = 0 := by
  rw [characterRulingTorusSubfan, Fan.subfan_cones]
  constructor
  · intro hσ'
    have hσ := (f).preimageCones_subset S₀ hσ'
    have hleast := ((f).mem_preimageCones_iff S₀ hσ).mp hσ'
    refine ⟨hσ, fun x hx ↦ ?_⟩
    rw [Set.mem_singleton_iff] at hleast
    have hx' := (f).mapsTo_leastCone hσ hx
    have hx₀ := (Submodule.mem_bot (R := NNReal)).mp (hleast ▸ hx')
    simpa using congrFun hx₀ 0
  · rintro ⟨hσ, hm⟩
    apply ((f).mem_preimageCones_iff S₀ hσ).mpr
    refine Set.mem_singleton_iff.mpr (le_bot_iff.mp ?_)
    apply (f).leastCone_le hσ (Fan.bot_mem_projectiveSpace_cones _ _)
    rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot (R := NNReal)).mpr (funext fun j ↦ by simp [hm x hx])

/-- The inclusion of the torus subfan identifies its cone charts with the ambient cone charts. -/
@[reassoc]
theorem affineToricChartι_comp_characterRulingTorusSubfanInclusion (σ : (U).cones) :
    (U).affineToricChartι σ ≫ (Φ.characterRulingTorusSubfanInclusion m h).algebraicMap =
      Φ.affineToricChartι
        ⟨σ.val, ((Φ.mem_characterRulingTorusSubfan_cones_iff m h).mp σ.property).1⟩ :=
  affineToricChartι_comp_subfanInclusion_algebraicMap _ _ _ _ σ

/-- The zero cone lies over the dense torus of the ruling base. -/
theorem bot_mem_characterRulingTorusSubfan (h₀ : Nonempty Φ.cones) :
    (⊥ : PointedCone ℝ V) ∈ (U).cones := by
  refine (Φ.mem_characterRulingTorusSubfan_cones_iff m h).2 ⟨Φ.bot_mem h₀.some.property, ?_⟩
  intro x hx
  simp [(Submodule.mem_bot (R := NNReal)).mp hx]

/-- The dense torus of a fan included in the inverse image of the base torus. -/
def denseTorusιRulingTorus (h₀ : Nonempty Φ.cones) :
    Φ.denseTorus ⟶ pullback (Φ.characterRuling m h) projectiveLineTorusι :=
  (U).affineToricChartι ⟨⊥, Φ.bot_mem_characterRulingTorusSubfan m h h₀⟩ ≫
    (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback.hom

/-- The dense torus in the ruling neighborhood is the zero-cone chart of the open subfan. -/
theorem denseTorusιRulingTorus_def (h₀ : Nonempty Φ.cones) :
    Φ.denseTorusιRulingTorus m h h₀ =
      (U).affineToricChartι ⟨⊥, Φ.bot_mem_characterRulingTorusSubfan m h h₀⟩ ≫
        (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback.hom := (rfl)

/-- The inclusion into the ruling neighborhood recovers the ambient dense torus. -/
@[reassoc (attr := simp)]
theorem denseTorusιRulingTorus_fst (h₀ : Nonempty Φ.cones) :
    Φ.denseTorusιRulingTorus m h h₀ ≫ pullback.fst _ _ = Φ.denseTorusι h₀ := by
  rw [denseTorusιRulingTorus, Category.assoc, IsPullback.isoPullback_hom_fst,
    affineToricChartι_comp_characterRulingTorusSubfanInclusion,
    denseTorusι_eq_affineToricChartι Φ h₀ (Φ.bot_mem h₀.some.property)]

private def splitCoordinates (R : Type) [Semiring R] :
    (Fin 2 → R) ≃ₗ[R] (Fin 1 → R) × (Fin 1 → R) :=
  (LinearEquiv.finTwoArrow R R).trans
    ((LinearEquiv.funUnique (Fin 1) R R).symm.prodCongr
      (LinearEquiv.funUnique (Fin 1) R R).symm)

variable (b : Basis (Fin 2) ℤ N)
  (hm : m = (b.coord 1).toAddMonoidHom)
  (hpos : hull ℝ {i (b 0)} ∈ Φ.cones) (hneg : hull ℝ {-i (b 0)} ∈ Φ.cones)

local notation "bℝ" => Φ.lattice.isBaseChange.basis b
local notation "eℝ" => LinearEquiv.trans (Basis.equivFun (Φ.lattice.isBaseChange.basis b))
  (splitCoordinates ℝ)
local notation "eℤ" => LinearEquiv.trans (Basis.equivFun b) (splitCoordinates ℤ)

private theorem splitCoordinates_map_lattice (x : N) :
    eℝ (i x) = ((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
      ((Int.castAddHom ℝ).compLeft (Fin 1)) (eℤ x) := by
  ext j <;> simp [splitCoordinates, Basis.equivFun_apply, ← Basis.coord_apply,
    ← IsIntegralLattice.realCharacter_coord Φ.lattice]

private theorem realBasis_zero : (bℝ) 0 = i (b 0) :=
  IsBaseChange.basis_apply b Φ.lattice.isBaseChange 0

private theorem splitCoordinates_apply_pivot : eℝ (i (b 0)) = ((1 : Fin 1 → ℝ), 0) := by
  rw [← realBasis_zero Φ b]
  ext j <;> simp [splitCoordinates, Basis.equivFun_apply]

include hm hpos hneg in
/-- In an adapted basis, the torus subfan consists of the origin and the two opposite rays. -/
theorem mem_characterRulingTorusSubfan_cones_iff_eq_bot_or_opposite_rays {σ : PointedCone ℝ V} :
    σ ∈ (U).cones ↔ σ = ⊥ ∨ σ = hull ℝ {i (b 0)} ∨ σ = hull ℝ {-i (b 0)} := by
  rw [mem_characterRulingTorusSubfan_cones_iff, hm, IsIntegralLattice.realCharacter_coord Φ.lattice]
  have hb (x : V) (hx : (bℝ).coord 1 x = 0) : x = (bℝ).coord 0 x • i (b 0) := by
    conv_lhs => rw [← (bℝ).sum_repr x, Fin.sum_univ_two]
    have hz : (bℝ).repr x 1 = 0 := hx
    rw [hz, zero_smul, add_zero, realBasis_zero Φ b, Basis.coord_apply]
  constructor
  · rintro ⟨hσ, hker⟩
    by_cases hp : i (b 0) ∈ σ
    · right
      left
      have hle : σ ≤ hull ℝ {i (b 0)} := by
        intro x hx
        refine mem_hull_singleton.mpr ⟨_, ?_, (hb x (hker x hx)).symm⟩
        by_contra! hn
        have hz : -i (b 0) ∈ σ := by
          have he := congrArg ((-(bℝ).coord 0 x)⁻¹ • ·) (hb x (hker x hx))
          rw [smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hn.ne, neg_one_smul] at he
          have hscale : 0 ≤ -((bℝ).coord 0 x)⁻¹ := by
            rw [← inv_neg]
            exact inv_nonneg.mpr (neg_nonneg.mpr hn.le)
          exact he ▸ σ.smul_mem hscale hx
        exact (Φ.isToricCone hσ).salient _ hp
          (fun h0 ↦ b.ne_zero 0 (Φ.lattice.injective (h0.trans (map_zero i).symm))) hz
      exact le_antisymm hle (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hp))
    · have hle : σ ≤ hull ℝ {-i (b 0)} := by
        intro x hx
        refine mem_hull_singleton.mpr ⟨-(bℝ).coord 0 x, neg_nonneg.mpr ?_, ?_⟩
        · by_contra! hn
          apply hp
          have he := congrArg (((bℝ).coord 0 x)⁻¹ • ·) (hb x (hker x hx))
          rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul] at he
          exact he ▸ σ.smul_mem (inv_nonneg.mpr hn.le) hx
        · simpa only [neg_smul, smul_neg, neg_neg] using (hb x (hker x hx)).symm
      exact ((Φ.isFaceOf_of_le hneg hσ hle).eq_bot_or_eq_of_hull_singleton _).imp_right Or.inr
  · rintro (rfl | rfl | rfl)
    · exact ⟨Φ.bot_mem hpos, by simp⟩
    · refine ⟨hpos, ?_⟩
      intro x hx
      obtain ⟨r, -, rfl⟩ := mem_hull_singleton.mp hx
      rw [map_smul, ← realBasis_zero Φ b]
      simp
    · refine ⟨hneg, ?_⟩
      intro x hx
      obtain ⟨r, -, rfl⟩ := mem_hull_singleton.mp hx
      rw [map_smul, map_neg, ← realBasis_zero Φ b]
      simp

private theorem map_ray_eq_prod (v : V) (w : Fin 1 → ℝ) (hv : eℝ v = (w, 0)) :
    (hull ℝ {v}).map (eℝ).toLinearMap =
      (hull ℝ {w}).prod (⊥ : PointedCone ℝ (Fin 1 → ℝ)) := by
  rw [PointedCone.map, Submodule.map_span, Set.image_singleton]
  -- The restricted linear map has the same value at the generator.
  have he : (↑(eℝ).toLinearMap : V →ₗ[Nonneg ℝ] ((Fin 1 → ℝ) × (Fin 1 → ℝ))) v = (w, 0) := hv
  rw [he, ← Submodule.map_inl, Submodule.map_span, Set.image_singleton]
  rfl

private theorem mem_product_cones_iff {σ : PointedCone ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ))} :
    σ ∈ ((P).prod projectiveLineTorusFan).cones ↔
      σ = ⊥ ∨ σ = affineRayCone.prod ⊥ ∨ σ = negativeRayCone.prod ⊥ := by
  rw [Fan.mem_prod_cones, projectiveSpace_finOne_eq_projectiveLineFan]
  simp only [mem_projectiveLineTorusFan_cones, exists_eq_left, mem_projectiveLineFan_cones]
  constructor
  · rintro ⟨τ, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl Submodule.prod_bot
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨⊥, Or.inl rfl, Submodule.prod_bot.symm⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩

/-- In an adapted basis, the cones over the dense torus are the product of the projective-line
fan in the first coordinate and the zero-cone fan in the second. -/
def characterRulingTorusFanEquiv :
    FanEquiv U ((P).prod projectiveLineTorusFan) where
  latticeEquiv := (eℤ).toAddEquiv
  realEquiv := eℝ
  map_lattice := splitCoordinates_map_lattice Φ b
  map_mem σ := by
    rw [mem_product_cones_iff, mem_characterRulingTorusSubfan_cones_iff_eq_bot_or_opposite_rays
      Φ m h b hm hpos hneg]
    have hpos' := map_ray_eq_prod Φ b (i (b 0)) 1 (splitCoordinates_apply_pivot Φ b)
    have hneg' := map_ray_eq_prod Φ b (-i (b 0)) (-1) (by
      rw [map_neg, splitCoordinates_apply_pivot Φ b]
      simp only [Prod.neg_mk, neg_zero])
    have hinj : Function.Injective (PointedCone.map (eℝ).toLinearMap) :=
      Submodule.map_injective_of_injective (eℝ).injective
    have hbot : (⊥ : PointedCone ℝ V).map (eℝ).toLinearMap = ⊥ :=
      Submodule.map_bot _
    rw [affineRayCone_def, negativeRayCone_def, ← hpos', ← hneg', ← hbot]
    exact or_congr (hinj.eq_iff) (or_congr hinj.eq_iff hinj.eq_iff)

local notation "E" => Φ.characterRulingTorusFanEquiv m h b hm hpos hneg

/-- The product fan comparison uses the two integral coordinates of the adapted basis. -/
@[simp]
theorem characterRulingTorusFanEquiv_latticeEquiv_apply (x : N) :
    (E).latticeEquiv x = (fun _ ↦ b.coord 0 x, fun _ ↦ b.coord 1 x) := by
  ext j <;> simp [characterRulingTorusFanEquiv, splitCoordinates, Basis.equivFun_apply,
    ← Basis.coord_apply]

/-- The restriction of the ruling is the second projection in the adapted fan coordinates. -/
theorem snd_comp_characterRulingTorusFanEquiv :
    (FanHom.snd P projectiveLineTorusFan).comp (E).toFanHom =
      Φ.characterRulingTorusFanHom m h := by
  apply FanHom.ext
  ext x j
  simp [hm]

/-- The torus restriction of the ruling is a projective-line product over the coefficient
field. Its second projection is the restricted ruling. -/
theorem isPullback_characterRulingTorusProduct :
    IsPullback
      ((E).toFanHom.algebraicMap ≫ (FanHom.fst P projectiveLineTorusFan).algebraicMap ≫
        projectiveLineToricIso.hom)
      (Φ.characterRulingTorusFanHom m h).algebraicMap
      (projectiveLine ℂ ↘ base) (projectiveLineTorusFan.algebraicRealization ↘ base) := by
  refine isPullback_projectiveLineTorusProduct.of_iso'
    (asIso (E).toFanHom.algebraicMap) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, ← FanHom.algebraicMap_comp]
      using congrArg FanHom.algebraicMap (snd_comp_characterRulingTorusFanEquiv
        Φ m h b hm hpos hneg)
  · simp
  · simp

/-- Over the dense torus, the ruling is isomorphic to the projection from the product of the
projective line and the base torus. -/
def characterRulingTorusIso :
    pullback (Φ.characterRuling m h) projectiveLineTorusι ≅
      pullback (projectiveLine ℂ ↘ base) (projectiveLineTorusFan.algebraicRealization ↘ base) :=
  (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback.symm ≪≫
    (Φ.isPullback_characterRulingTorusProduct m h b hm hpos hneg).isoPullback

/-- The first projection of the ruling product is the first adapted fan coordinate. -/
@[reassoc]
theorem isoPullback_hom_comp_characterRulingTorusIso_hom_fst :
    (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback.hom ≫
        (Φ.characterRulingTorusIso m h b hm hpos hneg).hom ≫ pullback.fst _ _ =
      (E).toFanHom.algebraicMap ≫ (FanHom.fst P projectiveLineTorusFan).algebraicMap ≫
        projectiveLineToricIso.hom := by
  rw [characterRulingTorusIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, IsPullback.isoPullback_hom_fst]

include hm hpos hneg in
private theorem rulingTorus_firstCoordinate_sign (σ : (U).cones) :
    (∀ x ∈ σ.val, 0 ≤ (U).lattice.realCharacter (b.coord 0).toAddMonoidHom x) ∨
      ∀ x ∈ σ.val, (U).lattice.realCharacter (b.coord 0).toAddMonoidHom x ≤ 0 := by
  have hb : (U).lattice.realCharacter (b.coord 0).toAddMonoidHom (i (b 0)) = 1 := by
    have hcoord (x : V) : (U).lattice.realCharacter (b.coord 0).toAddMonoidHom x =
        (Φ.lattice.isBaseChange.basis b).coord 0 x :=
      DFunLike.congr_fun (Φ.lattice.realCharacter_coord b 0) x
    have hbR : i (b 0) = (Φ.lattice.isBaseChange.basis b) 0 :=
      (IsBaseChange.basis_apply b Φ.lattice.isBaseChange 0).symm
    rw [hcoord, hbR]
    simp
  rcases (Φ.mem_characterRulingTorusSubfan_cones_iff_eq_bot_or_opposite_rays
    m h b hm hpos hneg).mp σ.property with hσ | hσ | hσ
  · left
    intro x hx
    have hx₀ : x = 0 := (Submodule.mem_bot _).mp (hσ ▸ hx)
    simp [hx₀]
  · left
    intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_hull_singleton.mp (hσ ▸ hx)
    simpa only [map_smul, hb, smul_eq_mul, mul_one] using hr
  · right
    intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_hull_singleton.mp (hσ ▸ hx)
    simpa only [map_smul, map_neg, hb, smul_eq_mul, mul_neg, mul_one, neg_nonpos] using hr

private theorem rulingTorus_firstCoordinate_eq :
    (E).toFanHom.algebraicMap ≫ (FanHom.fst P projectiveLineTorusFan).algebraicMap ≫
      projectiveLineToricIso.hom =
    (U).characterRuling (b.coord 0).toAddMonoidHom
      (rulingTorus_firstCoordinate_sign Φ m h b hm hpos hneg) := by
  have hf : (FanHom.fst P projectiveLineTorusFan).comp (E).toFanHom =
      (U).characterFanHom (b.coord 0).toAddMonoidHom
        (rulingTorus_firstCoordinate_sign Φ m h b hm hpos hneg) := by
    apply FanHom.ext
    ext x j
    simp
  rw [characterRuling_def, ← Category.assoc, ← FanHom.algebraicMap_comp, hf]

/-- In an affine chart of the ruling subfan, the first product coordinate is the
monomial of the first dual basis vector, with sign chosen for the projective-line chart. -/
@[reassoc]
theorem affineToricChartι_comp_characterRulingTorusIso_fst (σ : (U).cones) (j : Fin 2)
    (ha : (if j = 0 then (b.coord 0).toAddMonoidHom else -(b.coord 0).toAddMonoidHom) ∈
      dualSemigroup (U).lattice σ.val) :
    (U).affineToricChartι σ ≫ (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback.hom ≫
        (Φ.characterRulingTorusIso m h b hm hpos hneg).hom ≫ pullback.fst _ _ =
      projectiveLine.polynomialPoint ℂ (algebraMap ℂ (affineCoordinateRing (U).lattice σ.val)) j
        (MonoidAlgebra.of ℂ _ (Multiplicative.ofAdd ⟨_, ha⟩)) := by
  rw [Φ.isoPullback_hom_comp_characterRulingTorusIso_hom_fst,
    rulingTorus_firstCoordinate_eq Φ m h b hm hpos hneg,
    (U).affineToricChartι_comp_characterRuling _ _ σ j ha, projectiveLine.polynomialPoint_def]
  rfl

/-- The product comparison intertwines the projections to the base torus. -/
@[reassoc (attr := simp)]
theorem characterRulingTorusIso_hom_snd :
    (Φ.characterRulingTorusIso m h b hm hpos hneg).hom ≫ pullback.snd _ _ =
      pullback.snd (Φ.characterRuling m h) projectiveLineTorusι := by
  rw [characterRulingTorusIso, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
  rw [Iso.symm_hom, Iso.inv_comp_eq]
  exact (Φ.isPullback_characterRulingTorusSubfan m h).isoPullback_hom_snd.symm

/-- The scheme fiber over `[1 : a]`, for `a ≠ 0`, is the projective line in the adapted
coordinates. This is the fiber through a binomial center for `a = -c⁻¹`. -/
def characterRulingNonzeroFiberIso (a : ℂˣ) :
    pullback (Φ.characterRuling m h) (projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (a : ℂ)) ≅
      projectiveLine ℂ := by
  have hp := IsPullback.of_hasPullback (Φ.characterRulingTorusFanHom m h).algebraicMap
    (projectiveLineTorusPoint a)
  have hX := hp.paste_horiz (Φ.isPullback_characterRulingTorusSubfan m h)
  have hP := hp.paste_horiz (Φ.isPullback_characterRulingTorusProduct m h b hm hpos hneg)
  rw [projectiveLineTorusPoint_comp_projectiveLineTorusι] at hX
  rw [projectiveLineTorusPoint_comp_over] at hP
  exact hX.isoPullback.symm ≪≫ hP.isoPullback ≪≫ asIso (pullback.fst _ _)

/-- The fiber identification is an isomorphism over the coefficient field. -/
@[reassoc]
theorem characterRulingNonzeroFiberIso_hom_comp_over (a : ℂˣ) :
    (Φ.characterRulingNonzeroFiberIso m h b hm hpos hneg a).hom ≫ (projectiveLine ℂ ↘ base) =
      pullback.snd (Φ.characterRuling m h)
        (projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (a : ℂ)) := by
  dsimp only [characterRulingNonzeroFiberIso]
  simp only [Iso.trans_hom, Category.assoc, asIso_hom, pullback.condition, Category.comp_id,
    IsPullback.isoPullback_hom_snd, Iso.symm_hom, IsPullback.isoPullback_inv_snd]

/-- For a primitive pivot vector, the complementary coordinate of the ruling can be normalized
to the given surjective character. Thus the ruling above the dense torus is a projective-line
product as soon as both pivot rays are present. -/
theorem exists_characterRulingTorusIso_of_isPrimitive
    (hdim : finrank ℤ N = 2) {v : N} (hv : IsPrimitive v) (hmv : m v = 0)
    (hsurj : Function.Surjective m) (hvpos : hull ℝ {i v} ∈ Φ.cones)
    (hvneg : hull ℝ {-i v} ∈ Φ.cones) :
    ∃ e : pullback (Φ.characterRuling m h) projectiveLineTorusι ≅
      pullback (projectiveLine ℂ ↘ base) (projectiveLineTorusFan.algebraicRealization ↘ base),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  have := Φ.lattice.free
  have := Φ.lattice.finite
  obtain ⟨d, hd, he⟩ := (Module.finBasisOfFinrankEq ℤ N hdim).exists_basis_zero_eq_coord_one_eq
    hv hmv hsurj
  rw [← hd] at hvpos hvneg
  exact ⟨Φ.characterRulingTorusIso m h d he hvpos hvneg,
    Φ.characterRulingTorusIso_hom_snd m h d he hvpos hvneg⟩

end Fan

end TauCeti.Toric
