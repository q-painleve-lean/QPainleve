/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.Geometry.Toric.Algebraic.Examples.ProjectiveLine
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj

import Mathlib.RingTheory.Polynomial.Ideal
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
Varieties*, §1.4, and Tau Ceti's `Fan.projectiveSpaceToProj`.
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

namespace Fan

local notation "𝒜₁" => TauCeti.SymmetricAlgebra.homogeneousSubmodule ℂ (Option (Fin 1) → ℂ)
local notation "X₁" k => _root_.SymmetricAlgebra.ι ℂ (Option (Fin 1) → ℂ) (Pi.single k 1)

private abbrev rulingLinearEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] (Option (Fin 1) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv 1).symm

private theorem gradedMap_rulingLinearEquiv_coord (k : Fin 2) :
    _root_.SymmetricAlgebra.gradedMap ℂ rulingLinearEquiv.toLinearMap
      (projectiveLine.coord ℂ k) = X₁ (finSuccEquiv 1 k) := by
  have hcoord : projectiveLine.coord ℂ k =
      _root_.SymmetricAlgebra.ι ℂ (Fin 2 → ℂ) (Pi.single k 1) := by
    fin_cases k <;> simp [projectiveLine.ι_eq_smul_coord_add_smul_coord ℂ 0]
  rw [hcoord, _root_.SymmetricAlgebra.gradedMap_apply, _root_.SymmetricAlgebra.map_apply_ι]
  congr 1
  ext j
  simp [rulingLinearEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Pi.single_apply, Equiv.symm_apply_eq]

private theorem rulingReindex_pointCoordinates (k : Fin 2) :
    (projectiveSpaceHomogeneousCoordinates b₁ h₁ (k := finSuccEquiv 1 k) le_rfl).toRingHom.comp
        (_root_.SymmetricAlgebra.gradedMap ℂ rulingLinearEquiv.toLinearMap).toRingHom =
      projectiveLine.pointCoordinates ℂ (algebraMap ℂ _) k
        (projectiveSpaceRatioMonomial b₁ h₁
          (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) := by
  let e := rulingLinearEquiv
  let j := finSuccEquiv 1 k
  let g := projectiveSpaceHomogeneousCoordinates b₁ h₁ (k := j) le_rfl
  let a := projectiveSpaceRatioMonomial b₁ h₁ (k := j) le_rfl (finSuccEquiv 1 k.rev)
  let p : _root_.SymmetricAlgebra ℂ (Fin 2 → ℂ) →ₐ[ℂ] _ :=
    { toRingHom := projectiveLine.pointCoordinates ℂ (algebraMap ℂ _) k a
      commutes' := projectiveLine.pointCoordinates_algebraMap ℂ _ k a }
  have hh : g.comp (_root_.SymmetricAlgebra.map ℂ e.toLinearMap) = p := by
    apply _root_.SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    -- Compare the two algebra maps on a degree-one generator.
    change g (_root_.SymmetricAlgebra.map ℂ e.toLinearMap
        (_root_.SymmetricAlgebra.ι ℂ (Fin 2 → ℂ) v)) =
      p (_root_.SymmetricAlgebra.ι ℂ (Fin 2 → ℂ) v)
    rw [projectiveLine.ι_eq_smul_coord_add_smul_coord ℂ k v]
    simp only [map_add, map_smul]
    have hcoords (l : Fin 2) :
        _root_.SymmetricAlgebra.map ℂ e.toLinearMap (projectiveLine.coord ℂ l) =
          X₁ (finSuccEquiv 1 l) :=
      (_root_.SymmetricAlgebra.gradedMap_apply ℂ _ _).symm.trans
        (gradedMap_rulingLinearEquiv_coord l)
    have hp (l : Fin 2) : p (projectiveLine.coord ℂ l) =
        projectiveLine.pointCoordinates ℂ (algebraMap ℂ _) k a
          (projectiveLine.coord ℂ l) := (rfl)
    rw [hcoords, hcoords, hp, hp]
    simp [g, j, a, projectiveSpaceHomogeneousCoordinates_coord]
  rw [_root_.SymmetricAlgebra.gradedMap_toRingHom]
  exact congrArg AlgHom.toRingHom hh

private theorem projectiveSpaceChartToProj_comp_rulingReindex (k : Fin 2) :
    projectiveSpaceChartToProj b₁ h₁
        (k := finSuccEquiv 1 k)
        (le_rfl : (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val ≤ _) ≫
      (Proj.symmetricAlgebraMapIso ℂ rulingLinearEquiv).hom =
    projectiveLine.polynomialPoint ℂ (algebraMap ℂ _) k
      (projectiveSpaceRatioMonomial b₁ h₁
        (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) := by
  let e := rulingLinearEquiv
  let f := _root_.SymmetricAlgebra.gradedMap ℂ e.toLinearMap
  let j := finSuccEquiv 1 k
  let C := projectiveLine.coord ℂ k
  have hcoord : f C = X₁ j := gradedMap_rulingLinearEquiv_coord k
  have hsurj : Function.Surjective f := by
    simpa only [f, Function.Surjective, _root_.SymmetricAlgebra.gradedMap_apply] using
      _root_.SymmetricAlgebra.map_surjective ℂ e.toLinearMap e.surjective
  have hI := HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj
  let g := projectiveSpaceHomogeneousCoordinates b₁ h₁ (k := j) le_rfl
  have hu : IsUnit (g.toRingHom (f C)) := by
    rw [hcoord]
    exact isUnit_projectiveSpaceHomogeneousCoordinates_coord le_rfl le_rfl
  have hcoords :
      g.toRingHom.comp f.toRingHom = projectiveLine.pointCoordinates ℂ (algebraMap ℂ _) k
        (projectiveSpaceRatioMonomial b₁ h₁ (k := j) le_rfl (finSuccEquiv 1 k.rev)) :=
    rulingReindex_pointCoordinates k
  rw [projectiveSpaceChartToProj_self, projectiveSpaceAwayEquiv_toRingHom,
    Proj.symmetricAlgebraMapIso_hom,
    Proj.SpecMap_awayLift_awayι_eq _ _ one_pos (f.map_mem (projectiveLine.coord_mem ℂ k))
      one_pos _ hu, Category.assoc]
  erw [Proj.awayι_comp_map f hI one_pos C (projectiveLine.coord_mem ℂ k)]
  rw [projectiveLine.polynomialPoint_eq_awayLift]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, Away.lift_comp_map]
  congr 3
  refine Away.lift_eq_of_forall_mem _ _ 1 (fun n x _ ↦ ?_)
    (projectiveLine.coord_mem ℂ k) _ _
  simpa only [one_pow, Units.val_one, one_mul] using DFunLike.congr_fun hcoords x

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
    Φ.algebraicRealization ⟶ projectiveLine ℂ :=
  (Φ.characterFanHom m h).algebraicMap ≫ projectiveSpaceToProj b₁ h₁ ≫
    (Proj.symmetricAlgebraMapIso ℂ rulingLinearEquiv).hom

/-- The character morphism is a morphism over the coefficient field. -/
instance isOver_characterRuling : (Φ.characterRuling m h).IsOver (Spec (.of ℂ)) where
  comp_over := by
    rw [characterRuling, Category.assoc, Category.assoc]
    rw [TauCeti.SymmetricAlgebra.over_eq_projToSpec, Proj.symmetricAlgebraMapIso_hom_projToSpec,
      ← TauCeti.SymmetricAlgebra.over_eq_projToSpec, CategoryTheory.comp_over,
      CategoryTheory.comp_over]

private theorem characterFanHom_mapsTo (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val) :
    Set.MapsTo (Φ.characterFanHom m h).realMap (σ.val : Set V)
      (projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)).val := by
  intro x hx
  have hx' := (mem_dualSemigroup Φ.lattice _).1 hm hx
  -- Use the underlying cone of the selected projective chart.
  change (Φ.characterFanHom m h).realMap x ∈ projectiveSpaceCone b₁ i₁ {finSuccEquiv 1 k}ᶜ
  have hk : finSuccEquiv 1 (1 : Fin 2) = some 0 := (rfl)
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨l, rfl⟩
  · rw [finSuccEquiv_zero, projectiveSpaceCone_compl_none_finOne, mem_affineRayCone_iff]
    simpa only [ite_true, characterFanHom_realMap] using hx'
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    -- The successor of the only rank-one index is the second projective coordinate.
    have hs : (0 : Fin 1).succ = (1 : Fin 2) := (rfl)
    rw [hs, hk, projectiveSpaceCone_compl_some_finOne, mem_negativeRayCone_iff]
    simpa [hs] using hx'

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
    Φ.affineToricChartι σ ≫ Φ.characterRuling m h =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval
        (MonoidAlgebra.of ℂ _ (ofAdd ⟨_, hm⟩))).toRingHom) ≫
        projectiveLine.polynomialChartι ℂ k := by
  let τ := projectiveSpaceMaximalCone b₁ h₁ (finSuccEquiv 1 k)
  let f := Φ.characterFanHom m h
  have hστ := Φ.characterFanHom_mapsTo m h σ k hm
  have ha := congrArg (· ≫ projectiveSpaceToProj b₁ h₁ ≫
    (Proj.symmetricAlgebraMapIso ℂ rulingLinearEquiv).hom)
    (f.affineToricChartι_comp_algebraicMap_of_mapsTo σ τ hστ)
  simp only [Category.assoc] at ha
  rw [characterRuling, ha,
    affineToricChartι_comp_projectiveSpaceToProj_assoc τ le_rfl,
    projectiveSpaceChartToProj_comp_rulingReindex, projectiveLine.polynomialPoint_def,
    affineToricSchemeMap_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hb : (affineCoordinateRingMap Φ.lattice h₁ f.latticeMap f.realMap f.map_lattice hστ).comp
      (Polynomial.aeval (projectiveSpaceRatioMonomial b₁ h₁
        (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev))) =
      Polynomial.aeval (MonoidAlgebra.of ℂ _ (ofAdd ⟨_, hm⟩)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, MonoidAlgebra.of_apply,
      projectiveSpaceRatioMonomial_def, affineCoordinateRingMap_single]
    congr 3
    apply Subtype.ext
    rw [coe_dualSemigroupMap]
    exact Φ.characterFanHom_ratioCharacter m h k
  have heval : Polynomial.eval₂RingHom (algebraMap ℂ (affineCoordinateRing h₁ τ.val))
      (projectiveSpaceRatioMonomial b₁ h₁ (k := finSuccEquiv 1 k) le_rfl (finSuccEquiv 1 k.rev)) =
      (Polynomial.aeval _).toRingHom := (rfl)
  rw [heval]
  exact congrArg (fun φ : Polynomial ℂ →+* affineCoordinateRing Φ.lattice σ.val ↦
    Spec.map (CommRingCat.ofHom φ) ≫ projectiveLine.polynomialChartι ℂ k)
    (congrArg AlgHom.toRingHom hb)

/-- The scheme fiber over a point of the selected projective chart is cut out on the cone
chart by the corresponding character minus the affine coordinate of the point. -/
theorem comap_ker_characterRuling_polynomialPoint (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val) (c : ℂ) :
    (projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) k c).ker.comap
        (Φ.affineToricChartι σ ≫ Φ.characterRuling m h) =
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span {MonoidAlgebra.of ℂ _ (ofAdd ⟨_, hm⟩) - algebraMap ℂ _ c}).map
          (Scheme.ΓSpecIso (.of (affineCoordinateRing Φ.lattice σ.val))).inv.hom) := by
  rw [affineToricChartι_comp_characterRuling Φ m h σ k hm, projectiveLine.polynomialPoint_def,
    Scheme.Hom.ker_comp, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_map_of_isOpenImmersion, Scheme.Hom.ker_Spec_map]
  -- Evaluation at a scalar has kernel generated by the difference from the chart variable.
  rw [CommRingCat.hom_ofHom, ← Polynomial.evalRingHom, Polynomial.ker_evalRingHom,
    Scheme.IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv, Ideal.map_span, Set.image_singleton]
  simp

/-- On the dense torus the ruling has homogeneous coordinates `[1 : z^m]`. -/
theorem denseTorusι_comp_characterRuling (h₀ : Nonempty Φ.cones) :
    Φ.denseTorusι h₀ ≫ Φ.characterRuling m h =
      projectiveLine.polynomialPoint ℂ (algebraMap ℂ _) 0
        (MonoidAlgebra.of ℂ _ (ofAdd ((denseTorusDualEquiv Φ.lattice).symm m))) := by
  have hb := Φ.bot_mem h₀.some.property
  let σ : Φ.cones := ⟨⊥, hb⟩
  have hm : (if (0 : Fin 2) = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val := by
    simp [σ]
  rw [Φ.denseTorusι_eq_affineToricChartι h₀ hb,
    Φ.affineToricChartι_comp_characterRuling m h σ 0 hm, projectiveLine.polynomialPoint_def]
  congr 2
  have hχ : (⟨_, hm⟩ : dualSemigroup Φ.lattice σ.val) =
      (denseTorusDualEquiv Φ.lattice).symm m := by
    apply Subtype.ext
    simp [denseTorusDualEquiv_symm_apply]
  rw [hχ]
  rfl

end Fan
end TauCeti.Toric
