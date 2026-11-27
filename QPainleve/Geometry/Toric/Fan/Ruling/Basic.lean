/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.DenseTorus
public import QPainleve.Geometry.Toric.BaseChange.ProjectiveSpace
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine

import Mathlib.RingTheory.Polynomial.Ideal
import QPainleve.Geometry.Toric.BaseChange.Subfan
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap

/-!
# Toric morphisms to the projective line

A lattice character whose real extension has constant weak sign on each cone defines
a toric morphism to the projective-line fan. Its two affine chart coordinates pull back
to the character and its inverse, respectively. For a rank-two fan with opposite rays,
the determinant with the common ray direction supplies the character for the elementary
transformation of a toric surface.

The construction uses the toric morphism criterion in Fulton's *Introduction to Toric
Varieties*, §1.4, and `Fan.finiteFanSchemeToProjectiveSpace`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Multiplicative
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

local notation "b₁" => Pi.basisFun ℤ (Fin 1)
local notation "i₁" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 1)
local notation "h₁" => isIntegralLattice_intCast 1

private theorem projectiveSpaceCone_compl_none_finOne :
    projectiveSpaceCone b₁ i₁ {none}ᶜ = affineRayCone := by
  rw [projectiveSpaceCone_compl_none, affineRayCone_def]
  have hb (j : Fin 1) : i₁ (b₁ j) = 1 := by
    rw [Subsingleton.elim j 0, basisFun_finOne_eq_one, intCast_finOne_one]
  have he : Set.range (fun j ↦ i₁ (b₁ j)) = {1} := by
    simp only [hb, Set.range_const]
  rw [he]

private theorem projectiveSpaceCone_compl_some_finOne :
    projectiveSpaceCone b₁ i₁ {some (0 : Fin 1)}ᶜ = negativeRayCone := by
  have h : ({some (0 : Fin 1)}ᶜ : Set (Option (Fin 1))) = {none} := by
    ext j
    cases j
    · simp
    · simp [Subsingleton.elim (b := (0 : Fin 1))]
  rw [h, projectiveSpaceCone_def, negativeRayCone_def]
  have hb : i₁ (b₁ 0) = 1 := by
    rw [basisFun_finOne_eq_one, intCast_finOne_one]
  simp only [Set.image_singleton, projectiveSpaceGenerator_none, Fin.sum_univ_one, map_neg, hb]

/-- The projective-line chart at coordinate zero uses the positive ray, and
the chart at coordinate one uses the negative ray. -/
theorem projectiveSpaceMaximalCone_finOne_val (k : Fin 2) :
    (Fan.projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val =
      if k = 0 then affineRayCone else negativeRayCone := by
  fin_cases k
  · simpa using projectiveSpaceCone_compl_none_finOne
  · have hk : finSuccEquiv 1 (1 : Fin 2) = some 0 := (rfl)
    simpa [hk] using projectiveSpaceCone_compl_some_finOne

namespace Fan

variable (K : Type) [CommRing K]

local notation "𝒜₁" => TauCeti.SymmetricAlgebra.homogeneousSubmodule K (Option (Fin 1) → K)
local notation "X₁" k => _root_.SymmetricAlgebra.ι K (Option (Fin 1) → K) (Pi.single k 1)

private abbrev rulingLinearEquiv : (Fin 2 → K) ≃ₗ[K] (Option (Fin 1) → K) :=
  LinearEquiv.funCongrLeft K K (finSuccEquiv 1).symm

/-- The toric projective-space comparison in dimension one, with homogeneous coordinates
numbered by `Fin 2`. -/
def projectiveLineToricIso : (Fan.projectiveSpace b₁ h₁).finiteFanScheme K ≅ projectiveLine K :=
  asIso (finiteFanSchemeToProjectiveSpace K b₁ h₁) ≪≫
    Proj.symmetricAlgebraMapIso K (rulingLinearEquiv K)

/-- The toric comparison preserves the structure morphism to the coefficient field. -/
instance isOver_projectiveLineToricIso_hom :
    (projectiveLineToricIso K).hom.IsOver (Spec (.of K)) where
  comp_over := by
    simp only [projectiveLineToricIso, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [TauCeti.SymmetricAlgebra.over_eq_projToSpec, Proj.symmetricAlgebraMapIso_hom_projToSpec,
      ← TauCeti.SymmetricAlgebra.over_eq_projToSpec, CategoryTheory.comp_over]

/-- The rank-one projective-space fan consists of the zero cone and the two opposite rays. -/
theorem projectiveSpace_finOne_eq_projectiveLineFan :
    Fan.projectiveSpace b₁ h₁ = projectiveLineFan := by
  ext σ
  rw [mem_projectiveSpace_cones, mem_projectiveLineFan_cones]
  constructor
  · rintro ⟨S, hS, rfl⟩
    have hcases : S = ∅ ∨ S = {none}ᶜ ∨ S = {some (0 : Fin 1)}ᶜ := by
      by_cases h0 : none ∈ S <;> by_cases h1 : some (0 : Fin 1) ∈ S
      · exfalso
        apply hS
        ext (j | j)
        · simp [h0]
        · simpa only [Subsingleton.elim j 0, Set.mem_univ, iff_true] using h1
      · right
        right
        ext (j | j)
        · simp [h0]
        · simp [Subsingleton.elim j 0, h1]
      · right
        left
        ext (j | j)
        · simp [h0]
        · simp [Subsingleton.elim j 0, h1]
      · left
        ext (j | j)
        · simp [h0]
        · simp [Subsingleton.elim j 0, h1]
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl (projectiveSpaceCone_empty _)
    · exact Or.inr (Or.inl projectiveSpaceCone_compl_none_finOne)
    · exact Or.inr (Or.inr projectiveSpaceCone_compl_some_finOne)
  · rintro (rfl | rfl | rfl)
    · exact ⟨∅, by simp, projectiveSpaceCone_empty _⟩
    · exact ⟨{none}ᶜ, by simp, projectiveSpaceCone_compl_none_finOne⟩
    · exact ⟨{some 0}ᶜ, by simp, projectiveSpaceCone_compl_some_finOne⟩

private theorem gradedMap_rulingLinearEquiv_coord (k : Fin 2) :
    _root_.SymmetricAlgebra.gradedMap K (rulingLinearEquiv K).toLinearMap
      (projectiveLine.coord K k) = X₁ (finSuccEquiv 1 k) := by
  have hcoord : projectiveLine.coord K k =
      _root_.SymmetricAlgebra.ι K (Fin 2 → K) (Pi.single k 1) := by
    fin_cases k <;> simp [projectiveLine.ι_eq_smul_coord_add_smul_coord K 0]
  rw [hcoord, _root_.SymmetricAlgebra.gradedMap_apply, _root_.SymmetricAlgebra.map_apply_ι]
  congr 1
  ext j
  simp [rulingLinearEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Pi.single_apply, Equiv.symm_apply_eq]

private theorem rulingReindex_pointCoordinates (k : Fin 2) :
    (projectiveFanHomogeneousCoordinates K b₁ h₁ (k := finSuccEquiv 1 k) le_rfl).toRingHom.comp
        (_root_.SymmetricAlgebra.gradedMap K (rulingLinearEquiv K).toLinearMap).toRingHom =
      projectiveLine.pointCoordinates K (algebraMap K _) k
        (projectiveFanRatioMonomial K b₁ h₁
          (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) := by
  let e := rulingLinearEquiv K
  let j := finSuccEquiv 1 k
  let g := projectiveFanHomogeneousCoordinates K b₁ h₁ (k := j) le_rfl
  let a := projectiveFanRatioMonomial K b₁ h₁ (k := j) le_rfl (finSuccEquiv 1 k.rev)
  let p : _root_.SymmetricAlgebra K (Fin 2 → K) →ₐ[K] _ :=
    { toRingHom := projectiveLine.pointCoordinates K (algebraMap K _) k a
      commutes' := projectiveLine.pointCoordinates_algebraMap K _ k a }
  have hh : g.comp (_root_.SymmetricAlgebra.map K e.toLinearMap) = p := by
    apply _root_.SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    -- Compare the two algebra maps on a degree-one generator.
    change g (_root_.SymmetricAlgebra.map K e.toLinearMap
        (_root_.SymmetricAlgebra.ι K (Fin 2 → K) v)) =
      p (_root_.SymmetricAlgebra.ι K (Fin 2 → K) v)
    rw [projectiveLine.ι_eq_smul_coord_add_smul_coord K k v]
    simp only [map_add, map_smul]
    have hcoords (l : Fin 2) :
        _root_.SymmetricAlgebra.map K e.toLinearMap (projectiveLine.coord K l) =
          X₁ (finSuccEquiv 1 l) :=
      (_root_.SymmetricAlgebra.gradedMap_apply K _ _).symm.trans
        (gradedMap_rulingLinearEquiv_coord K l)
    have hp (l : Fin 2) : p (projectiveLine.coord K l) =
        projectiveLine.pointCoordinates K (algebraMap K _) k a
          (projectiveLine.coord K l) := (rfl)
    rw [hcoords, hcoords, hp, hp]
    simp [g, j, a, projectiveFanHomogeneousCoordinates_coord]
  rw [_root_.SymmetricAlgebra.gradedMap_toRingHom]
  exact congrArg AlgHom.toRingHom hh

private theorem projectiveSpaceChartToProj_comp_rulingReindex (k : Fin 2) :
    projectiveFanChartToProj K b₁ h₁
        (k := finSuccEquiv 1 k)
        (le_rfl : (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val ≤ _) ≫
      (Proj.symmetricAlgebraMapIso K (rulingLinearEquiv K)).hom =
    projectiveLine.polynomialPoint K (algebraMap K _) k
      (projectiveFanRatioMonomial K b₁ h₁
        (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) := by
  let e := rulingLinearEquiv K
  let f := _root_.SymmetricAlgebra.gradedMap K e.toLinearMap
  let j := finSuccEquiv 1 k
  let C := projectiveLine.coord K k
  have hcoord : f C = X₁ j := gradedMap_rulingLinearEquiv_coord K k
  have hsurj : Function.Surjective f := by
    simpa only [f, Function.Surjective, _root_.SymmetricAlgebra.gradedMap_apply] using
      _root_.SymmetricAlgebra.map_surjective K e.toLinearMap e.surjective
  have hI := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj
  let g := projectiveFanHomogeneousCoordinates K b₁ h₁ (k := j) le_rfl
  have hu : IsUnit (g.toRingHom (f C)) := by
    rw [hcoord]
    exact isUnit_projectiveFanHomogeneousCoordinates_coord K le_rfl le_rfl
  have hcoords :
      g.toRingHom.comp f.toRingHom = projectiveLine.pointCoordinates K (algebraMap K _) k
        (projectiveFanRatioMonomial K b₁ h₁ (k := j) le_rfl (finSuccEquiv 1 k.rev)) :=
    rulingReindex_pointCoordinates K k
  rw [projectiveFanChartToProj_self, projectiveFanAwayEquiv_toRingHom,
    Proj.symmetricAlgebraMapIso_hom,
    Proj.SpecMap_awayLift_awayι_eq _ _ one_pos (f.map_mem (projectiveLine.coord_mem K k))
      one_pos _ hu, Category.assoc]
  erw [Proj.awayι_comp_map f hI one_pos C (projectiveLine.coord_mem K k)]
  rw [projectiveLine.polynomialPoint_eq_awayLift]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, Away.lift_comp_map]
  congr 3
  refine Away.lift_eq_of_forall_mem _ _ 1 (fun n x _ ↦ ?_)
    (projectiveLine.coord_mem K k) _ _
  simpa only [one_pow, Units.val_one, one_mul] using DFunLike.congr_fun hcoords x

/-- The maximal cone chart corresponds to the polynomial chart at the same
homogeneous coordinate. -/
theorem range_affineToricChartι_comp_projectiveLineToricIso (k : Fin 2) :
    Set.range ((Fan.projectiveSpace b₁ h₁).affineChartι K
      (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)) ≫ (projectiveLineToricIso K).hom) =
      Set.range (projectiveLine.polynomialChartι K k) := by
  let e := Proj.symmetricAlgebraMapIso K (rulingLinearEquiv K)
  have he : e.hom ⁻¹ᵁ (projectiveLine.polynomialChartι K k).opensRange =
      (projectiveFanChartToProj K b₁ h₁
        (le_rfl : (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val ≤ _)).opensRange := by
    dsimp only [e]
    rw [projectiveLine.opensRange_polynomialChartι, Proj.symmetricAlgebraMapIso_hom,
      Proj.map_preimage_basicOpen, gradedMap_rulingLinearEquiv_coord,
      opensRange_projectiveFanChartToProj]
  rw [projectiveLineToricIso, Iso.trans_hom, asIso_hom,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace_assoc K
      (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)) le_rfl,
    ← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
  congr 1
  rw [Scheme.Hom.opensRange_comp, ← he, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_of_isIso, top_inf_eq]

/-- Under the toric comparison, the dense torus of the projective-line fan is the
intersection of the two standard polynomial charts. -/
theorem range_denseTorusι_comp_projectiveLineToricIso
    (h₀ : Nonempty (Fan.projectiveSpace b₁ h₁).cones) :
    Set.range ((Fan.projectiveSpace b₁ h₁).affineChartι K
      ⟨⊥, (Fan.projectiveSpace b₁ h₁).bot_mem h₀.some.property⟩ ≫ (projectiveLineToricIso K).hom) =
      Set.range (projectiveLine.polynomialChartι K 0) ∩
        Set.range (projectiveLine.polynomialChartι K 1) := by
  let σ := projectiveSpaceMaximalCone b₁ h₁ none
  let τ := projectiveSpaceMaximalCone b₁ h₁ (some 0)
  have hbotMem := Fan.bot_mem_projectiveSpace_cones b₁ h₁
  have hmeet : σ ⊓ τ = ⟨⊥, hbotMem⟩ := by
    apply Subtype.ext
    -- Infimum of fan cones is computed on the underlying cones.
    change projectiveSpaceCone b₁ i₁ {none}ᶜ ⊓ projectiveSpaceCone b₁ i₁ {some 0}ᶜ = ⊥
    rw [projectiveSpaceCone_compl_none_finOne, projectiveSpaceCone_compl_some_finOne,
      affineRayCone_inf_negativeRayCone]
  rw [← range_affineToricChartι_comp_projectiveLineToricIso K 0,
    ← range_affineToricChartι_comp_projectiveLineToricIso K 1]
  have himage (ρ : (Fan.projectiveSpace b₁ h₁).cones) :
      Set.range ((Fan.projectiveSpace b₁ h₁).affineChartι K ρ ≫ (projectiveLineToricIso K).hom) =
        (projectiveLineToricIso K).hom ''
          Set.range ((Fan.projectiveSpace b₁ h₁).affineChartι K ρ) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (Scheme.Hom.comp_apply _ _))
  have hinj : Function.Injective (projectiveLineToricIso K).hom :=
    (projectiveLineToricIso K).hom.homeomorph.injective
  rw [himage, himage, himage, ← Set.image_inter hinj,
    Fan.range_affineChartι_inter K]
  exact congrArg (fun ρ : (Fan.projectiveSpace b₁ h₁).cones ↦
    (projectiveLineToricIso K).hom '' Set.range ((Fan.projectiveSpace b₁ h₁).affineChartι K ρ))
      hmeet.symm

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (m : N →+ ℤ)

/-- A character that has constant weak sign on each cone determines a morphism to the
projective-line fan. -/
def characterFanHom
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0) :
    FanHom Φ (Fan.projectiveSpace b₁ h₁) where
  latticeMap := AddMonoidHom.pi fun _ : Fin 1 ↦ m
  realMap := LinearMap.pi fun _ : Fin 1 ↦ Φ.lattice.realCharacter m
  map_lattice n := by ext j; simp [IsIntegralLattice.realCharacter_apply]
  map_cone σ hσ := by
    rcases h ⟨σ, hσ⟩ with hσ | hσ
    · refine ⟨_, (projectiveSpaceMaximalCone b₁ h₁ none).property, ?_⟩
      -- Use the cone underlying the selected projective chart.
      change _ ≤ projectiveSpaceCone b₁ i₁ {none}ᶜ
      rw [projectiveSpaceCone_compl_none_finOne]
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_affineRayCone_iff _).2 (hσ x hx)
    · refine ⟨_, (projectiveSpaceMaximalCone b₁ h₁ (some 0)).property, ?_⟩
      -- Use the cone underlying the selected projective chart.
      change _ ≤ projectiveSpaceCone b₁ i₁ {some (0 : Fin 1)}ᶜ
      rw [projectiveSpaceCone_compl_some_finOne]
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_negativeRayCone_iff _).2 (hσ x hx)

variable (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
  ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)

/-- The map on the integral lattices sends a vector to its pairing with the character. -/
@[simp]
theorem characterFanHom_latticeMap (x : N) (j : Fin 1) :
    (Φ.characterFanHom m h).latticeMap x j = m x := (rfl)

/-- The real map to the projective-line fan is the real extension of the character. -/
@[simp]
theorem characterFanHom_realMap (x : V) (j : Fin 1) :
    (Φ.characterFanHom m h).realMap x j = Φ.lattice.realCharacter m x := (rfl)

/-- The morphism to the projective line given by a character with a constant weak sign on
each cone. On the dense torus its homogeneous coordinates are `[1 : z^m]`. -/
def characterRuling :
    Φ.finiteFanScheme K ⟶ projectiveLine K :=
  (Φ.characterFanHom m h).finiteFanSchemeHom K ≫ finiteFanSchemeToProjectiveSpace K b₁ h₁ ≫
    (Proj.symmetricAlgebraMapIso K (rulingLinearEquiv K)).hom

/-- The ruling is the toric character map followed by the projective-line comparison. -/
theorem characterRuling_def :
    Φ.characterRuling K m h =
      (Φ.characterFanHom m h).finiteFanSchemeHom K ≫ (projectiveLineToricIso K).hom :=
  (rfl)

/-- The character morphism is a morphism over the coefficient field. -/
instance isOver_characterRuling : (Φ.characterRuling K m h).IsOver (Spec (.of K)) where
  comp_over := by
    rw [characterRuling_def, CategoryTheory.comp_over]

private theorem characterFanHom_mapsTo (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val) :
    Set.MapsTo (Φ.characterFanHom m h).realMap (σ.val : Set V)
      (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val := by
  intro x hx
  have hx' := (mem_dualSemigroup Φ.lattice _).1 hm hx
  rw [projectiveSpaceMaximalCone_finOne_val]
  split_ifs at hx' ⊢
  · exact (mem_affineRayCone_iff _).2 (by simpa only [characterFanHom_realMap] using hx')
  · exact (mem_negativeRayCone_iff _).2 (by simpa using hx')

private theorem characterFanHom_ratioCharacter (k : Fin 2) :
    (projectiveSpaceRatioCharacter b₁ (finSuccEquiv 1 k.rev) (finSuccEquiv 1 k)).comp
        (Φ.characterFanHom m h).latticeMap =
      if k = 0 then m else -m := by
  have hk : finSuccEquiv 1 (1 : Fin 2) = some 0 := (rfl)
  have hneg : projectiveSpaceRatioCharacter b₁ none (some 0) =
      -(projectiveSpaceRatioCharacter b₁ (some 0) none) :=
    eq_neg_of_add_eq_zero_left (by rw [projectiveSpaceRatioCharacter_add,
      projectiveSpaceRatioCharacter_self])
  ext n
  fin_cases k <;> simp [hk, hneg, projectiveSpaceRatioCharacter_some_none]

/-- On a cone where `m` is nonnegative, the ruling is given in the chart `X₀ ≠ 0` by
the monomial of `m`. On a cone where `-m` is nonnegative, the chart `X₁ ≠ 0` instead uses
the monomial of `-m`. -/
theorem affineToricChartι_comp_characterRuling (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val) :
    Φ.affineChartι K σ ≫ Φ.characterRuling K m h =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval
        (AddMonoidAlgebra.single ⟨_, hm⟩ 1)).toRingHom) ≫
        projectiveLine.polynomialChartι K k := by
  let τ := projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)
  let f := Φ.characterFanHom m h
  have hστ := Φ.characterFanHom_mapsTo m h σ k hm
  have ha := congrArg (· ≫ finiteFanSchemeToProjectiveSpace K b₁ h₁ ≫
    (Proj.symmetricAlgebraMapIso K (rulingLinearEquiv K)).hom)
    (f.affineChartι_comp_finiteFanSchemeHom K σ τ hστ)
  simp only [Category.assoc] at ha
  rw [characterRuling, ha,
    affineChartι_comp_finiteFanSchemeToProjectiveSpace_assoc K τ le_rfl,
    projectiveSpaceChartToProj_comp_rulingReindex, projectiveLine.polynomialPoint_def,
    affineChartMap_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hb : (AddMonoidAlgebra.mapDomainAlgHom K K
      (dualSemigroupMap Φ.lattice h₁ f.latticeMap f.realMap f.map_lattice hστ)).comp
      (Polynomial.aeval (projectiveFanRatioMonomial K b₁ h₁
        (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev))) =
      Polynomial.aeval (AddMonoidAlgebra.single ⟨_, hm⟩ 1) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X,
      projectiveFanRatioMonomial_def, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    congr 3
    apply Subtype.ext
    rw [coe_dualSemigroupMap]
    exact Φ.characterFanHom_ratioCharacter m h k
  have heval : Polynomial.eval₂RingHom (algebraMap K (affineChartRing K h₁ τ.val))
      (projectiveFanRatioMonomial K b₁ h₁ (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) =
      (Polynomial.aeval _).toRingHom := (rfl)
  rw [heval]
  exact congrArg (fun φ : Polynomial K →+* affineChartRing K Φ.lattice σ.val ↦
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLine.polynomialChartι K k)
    (congrArg AlgHom.toRingHom hb)

/-- The scheme fiber over a point of the selected projective chart is cut out on the cone
chart by the corresponding character minus the affine coordinate of the point. -/
theorem comap_ker_characterRuling_polynomialPoint (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val) (c : K) :
    (projectiveLine.polynomialPoint K (RingHom.id K) k c).ker.comap
        (Φ.affineChartι K σ ≫ Φ.characterRuling K m h) =
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span {AddMonoidAlgebra.single ⟨_, hm⟩ 1 - algebraMap K _ c}).map
          (Scheme.ΓSpecIso (.of (affineChartRing K Φ.lattice σ.val))).inv.hom) := by
  rw [Φ.affineToricChartι_comp_characterRuling K m h σ k hm, projectiveLine.polynomialPoint_def,
    Scheme.Hom.ker_comp, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_map_of_isOpenImmersion, Scheme.Hom.ker_Spec_map]
  -- Evaluation at a scalar has kernel generated by the difference from the chart variable.
  rw [CommRingCat.hom_ofHom, ← Polynomial.evalRingHom, Polynomial.ker_evalRingHom,
    Scheme.IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_singleton]
  simp

/-- On the zero-cone chart the ruling has homogeneous coordinates `[1 : z^m]`. -/
theorem denseTorusι_comp_characterRuling (h₀ : Nonempty Φ.cones) :
    Φ.affineChartι K ⟨⊥, Φ.bot_mem h₀.some.property⟩ ≫ Φ.characterRuling K m h =
      projectiveLine.polynomialPoint K (algebraMap K _) 0
        (AddMonoidAlgebra.single ⟨m, by simp⟩ 1) := by
  let σ : Φ.cones := ⟨⊥, Φ.bot_mem h₀.some.property⟩
  have hm : (if (0 : Fin 2) = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val := by
    simp [σ]
  rw [Φ.affineToricChartι_comp_characterRuling K m h σ 0 hm, projectiveLine.polynomialPoint_def]
  rfl

/-- A nonzero character gives a dominant morphism to the projective line. -/
theorem isDominant_characterRuling [Nonempty Φ.cones] (hm : m ≠ 0) :
    IsDominant (Φ.characterRuling K m h) := by
  rw [characterRuling_def]
  let f := Φ.characterFanHom m h
  have hmul (y : Fin 1 → ℤ) : y = y 0 • b₁ 0 := by
    ext j
    rw [Subsingleton.elim j 0, basisFun_finOne_eq_one]
    simp
  have hdual : Function.Injective (fun a : (Fin 1 → ℤ) →+ ℤ ↦ a.comp f.latticeMap) := by
    intro a a' he
    obtain ⟨x, hx⟩ : ∃ x, m x ≠ 0 := by
      by_contra! hzero
      exact hm (AddMonoidHom.ext hzero)
    have hf : f.latticeMap x = m x • b₁ 0 := hmul (f.latticeMap x)
    have hba : a (b₁ 0) = a' (b₁ 0) := by
      apply mul_left_cancel₀ hx
      have hh := DFunLike.congr_fun he x
      change a (f.latticeMap x) = a' (f.latticeMap x) at hh
      rw [hf, map_zsmul, map_zsmul] at hh
      simpa only [Int.zsmul_eq_mul] using hh
    apply AddMonoidHom.ext
    intro y
    calc
      a y = a (y 0 • b₁ 0) := congrArg a (hmul y)
      _ = a' (y 0 • b₁ 0) := by simp only [map_zsmul, hba]
      _ = a' y := congrArg a' (hmul y).symm
  have := f.isDominant_finiteFanSchemeHom_of_injective_dualMap K inferInstance hdual
  exact inferInstanceAs (IsDominant (f.finiteFanSchemeHom K ≫ (projectiveLineToricIso K).hom))

end Fan

namespace FanHom

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

open Fan

/-- A fan morphism to the projective-line fan with lattice character `n`
is the character map induced by `n`. Its existence supplies the cone-wise sign
condition. -/
theorem exists_eq_characterFanHom
    (q : FanHom Φ (Fan.projectiveSpace b₁ h₁)) (n : N →+ ℤ) (hq : ∀ x j, q.latticeMap x j = n x) :
    ∃ hn, q = Φ.characterFanHom n hn := by
  let φ := (LinearMap.proj (0 : Fin 1)).comp q.realMap
  have hφ : φ = Φ.lattice.realCharacter n := by
    apply Φ.lattice.eq_realCharacter
    intro x
    simp [φ, q.map_lattice, hq]
  have he (x : V) : q.realMap x 0 = Φ.lattice.realCharacter n x :=
    DFunLike.congr_fun hφ x
  have hn (σ : Φ.cones) :
      (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter n x) ∨
        ∀ x ∈ σ.val, Φ.lattice.realCharacter n x ≤ 0 := by
    have hcones := congrArg Fan.cones projectiveSpace_finOne_eq_projectiveLineFan
    have hτ := (mem_projectiveLineFan_cones _).mp (hcones.subset (q.leastCone_mem σ.property))
    have hx (x : V) (hx : x ∈ σ.val) :
        q.realMap x ∈ q.leastCone σ.property :=
      q.map_le_leastCone σ.property ⟨x, hx, rfl⟩
    rcases hτ with hτ | hτ | hτ
    · exact Or.inl fun x h ↦ by
        have hzero : q.realMap x = 0 := (Submodule.mem_bot (Nonneg ℝ)).mp (hτ ▸ hx x h)
        simp [← he x, hzero]
    · exact Or.inl fun x h ↦ he x ▸ (mem_affineRayCone_iff _).mp (hτ ▸ hx x h)
    · exact Or.inr fun x h ↦ he x ▸ (mem_negativeRayCone_iff _).mp (hτ ▸ hx x h)
  refine ⟨hn, FanHom.ext ?_⟩
  ext x j
  rw [characterFanHom_latticeMap, hq]

local notation "m(" f ")" =>
  AddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 ↦ ℤ) 0) (FanHom.latticeMap f)

variable (K : Type) [CommRing K]

/-- On the zero-cone chart, the projective coordinates of a map to the projective-line
fan are `[1 : zᵐ]`, where `m` evaluates its lattice map at the sole coordinate. -/
@[reassoc]
theorem denseTorusι_comp_projectiveLineToricIso (f : FanHom Φ (Fan.projectiveSpace b₁ h₁))
    (hΦ : Nonempty Φ.cones) :
    Φ.affineChartι K ⟨⊥, Φ.bot_mem hΦ.some.property⟩ ≫
        f.finiteFanSchemeHom K ≫ (Fan.projectiveLineToricIso K).hom =
      projectiveLine.polynomialPoint K (algebraMap K _) 0
        (AddMonoidAlgebra.single ⟨m(f), by simp⟩ 1) := by
  obtain ⟨_, hf⟩ := f.exists_eq_characterFanHom m(f) fun x j ↦ by
    rw [Subsingleton.elim j 0]
    rfl
  conv_lhs => rw [hf, ← Fan.characterRuling_def K, Φ.denseTorusι_comp_characterRuling K _ _ hΦ]

end FanHom

end TauCeti.Toric
