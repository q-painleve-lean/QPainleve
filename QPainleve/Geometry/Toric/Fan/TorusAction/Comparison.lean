/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Evaluation
public import QPainleve.Geometry.Toric.Fan.TorusAction.Contraction

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Modification
import TauCeti.Geometry.Toric.Algebraic.Fan.Normal

/-!
# Comparing fixed-center X evaluations on contracted toric models

The Laurent-coordinate evaluation descends from the ordered internal blowups along a
modification. Equality of such rational evaluations identifies the difference between two
isomorphisms as a torus translation when the target charges have finite index. The comparison
uses the generic maps to the X torus, which need not be dominant.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "L" => LaurentRing ℂ (Fin n)
local notation "F" => Φ.algebraicRealization
local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "Y" a:arg => (Sigma.fst (internalBlowupTower b s (center a)))
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s (center a)))
local notation "π" a:arg => toBase (T a)
local notation "ι" a:arg => WithBoundary.boundaryι
  (Sigma.snd (internalBlowupTower b s (center a)))
local notation "m" j:arg => ofAdd (LinearMap.toAddMonoidHom
  (b.detDualEquiv (Ray.primitiveGenerator (s j))))
local notation "C" => algebraMap ℂ (Scheme.functionField F)

variable {X : Scheme} [IsIntegral X]

/-- Evaluation at the specified centers on a contraction of an ordered toric blowup
model. Its pullback to the model evaluates each Laurent coordinate as its scaled charge
character. -/
def contractedXEvaluation (c : Multiplicative (Fin n → ℤ) →* ℂˣ) (hΦ : Φ.IsRegular)
    (p : Y c ⟶ X) [IsModification p] : X ⤏ Spec (.of L) := by
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  exact (p.existsUnique_rationalMap_comp_eq_of_isModification
    ((π c).toRationalMap.comp (Φ.xEvaluation b s c))).exists.choose

variable (c d : Multiplicative (Fin n → ℤ) →* ℂˣ) (hΦ : Φ.IsRegular)
  {X' : Scheme} [IsIntegral X']
variable (p : (internalBlowupTower b s (fun j : Fin n ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X)
  [IsModification p]
  (q : (internalBlowupTower b s (fun j : Fin n ↦ d (ofAdd (Pi.single j 1)))).1 ⟶ X')
  [IsModification q]

/-- Pullback to the ordered blowup model recovers the original fixed-center evaluation. -/
theorem comp_contractedXEvaluation :
    letI := isIntegral_internalBlowupTower b s (center c) hΦ
    letI := isModification_internalBlowupTower_toBase b s (center c) hΦ
    p.toRationalMap.comp (contractedXEvaluation b s c hΦ p) =
      (π c).toRationalMap.comp (Φ.xEvaluation b s c) := by
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  exact (p.existsUnique_rationalMap_comp_eq_of_isModification
    ((π c).toRationalMap.comp (Φ.xEvaluation b s c))).exists.choose_spec

/-- The descended evaluation is over the complex base when the two projections
from the ordered model give the same structure morphism. -/
theorem contractedXEvaluation_isOver (f : X ⟶ S)
    (hf : p ≫ f = π c ≫ Φ.algebraicRealizationStructureMap) :
    (contractedXEvaluation b s c hΦ p).IsOver f (Spec.algebraMap ℂ L) := by
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  have hbase := Scheme.RationalMap.isOver_iff.mp
    (inferInstance : (Φ.xEvaluation b s c).IsOver
      (F ↘ S) (Spec.algebraMap ℂ L))
  apply Scheme.RationalMap.isOver_iff.mpr
  apply Scheme.RationalMap.comp_left_injective p.toRationalMap
  simpa only [Scheme.RationalMap.comp_compHom, comp_contractedXEvaluation,
    Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom,
    algebraicRealization_over, hf] using
    congrArg ((π c).toRationalMap.comp ·) hbase

/-- At the generic point the contracted evaluation is the scaled Laurent evaluation
transported through the function field isomorphism of the contraction. -/
@[simp]
theorem fromFunctionField_contractedXEvaluation :
    letI := isIntegral_internalBlowupTower b s (center c) hΦ
    letI := isModification_internalBlowupTower_toBase b s (center c) hΦ
    letI := p.isIso_functionFieldMap_of_isModification
    (contractedXEvaluation b s c hΦ p).fromFunctionField =
      Spec.map ((CommRingCat.ofHom (Φ.xEval b s c).toRingHom) ≫
        (π c).functionFieldMap ≫ inv p.functionFieldMap) := by
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  have := p.isIso_functionFieldMap_of_isModification
  have h := congrArg Scheme.RationalMap.fromFunctionField (comp_contractedXEvaluation b s c hΦ p)
  simp only [Scheme.RationalMap.fromFunctionField_comp,
    Scheme.Hom.functionFieldMap_toRationalMap, fromFunctionField_xEvaluation] at h
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← h, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

variable {D : X.IdealSheafData} {D' : X'.IdealSheafData}
  [X.Over S] [X'.Over S] [IsSeparated (X' ↘ S)]

section

variable (e : X ≅ X') [e.hom.IsOver S]

/-- Equality of fixed-center rational evaluations along a specified isomorphism of
contractions determines a unique translating character. Its ordered lift compares the
contraction projections and the Picard markings, and the isomorphism identifies the
reduced boundary ideals. The finite-index condition is on the charge lattice. -/
theorem existsUnique_translation_of_comp_contractedXEvaluation_eq
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (hc : p ≫ (X ↘ S) = π c ≫ Φ.algebraicRealizationStructureMap)
    (hd : q ≫ (X' ↘ S) = π d ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hD' : (D'.comap q).support = (ι d).ker.support)
    [IsReduced D.subscheme] [IsReduced D'.subscheme]
    (heval : e.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q) =
      contractedXEvaluation b s c hΦ p) :
    ∃! χ : Multiplicative (N →+ ℤ) →* ℂˣ, ∃ t : Y c ≅ Y d,
      IsLift (Φ.torusTranslation χ) (T c) (T d) t ∧
      p ≫ e.hom = t.hom ≫ q ∧ D'.comap e.hom = D ∧
      ∀ a : LineBundleClass X',
        (internalBlowupPicardMarking b s (center c) hΦ).symm
            (Additive.ofMul (LineBundleClass.pullback p (LineBundleClass.pullback e.hom a))) =
          (internalBlowupPicardMarking b s (center d) hΦ).symm
            (Additive.ofMul (LineBundleClass.pullback q a)) := by
  apply existsUnique_isLift_of_eq_scaled_characters_of_contractions b s (center c) (center d)
    hΦ hindex e hc hd hD hD'
  dsimp only
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isIntegral_internalBlowupTower b s (center d) hΦ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b s (center d) hΦ
  have := p.isIso_functionFieldMap_of_isModification
  have := q.isIso_functionFieldMap_of_isModification
  have h := congrArg Scheme.RationalMap.fromFunctionField heval
  simp only [Scheme.RationalMap.fromFunctionField_comp,
    Scheme.Hom.functionFieldMap_toRationalMap, fromFunctionField_contractedXEvaluation,
    ← Spec.map_comp, Spec.map_inj] at h
  intro j
  simpa only [Category.assoc, CommRingCat.comp_apply, CommRingCat.hom_comp,
    RingHom.comp_apply, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    xEval_X] using ConcreteCategory.congr_hom h (LaurentRing.X j : L)

end

/-- Two isomorphisms over ℂ from the same scheme into contractions of the same ordered
toric presentation have the same boundary pullback and marked Picard action if their
fixed-center rational evaluations agree and the target charge lattice has finite index.
The Picard comparison identifies a class on each target by the ordered coordinates
of its pullback to the corresponding internal blowup model. -/
theorem comap_boundary_and_pullback_eq_of_equal_contractedXEvaluation
    {W : Scheme} [W.Over S]
    (f : W ≅ X) (g : W ≅ X') [f.hom.IsOver S] [g.hom.IsOver S]
    (hindex : (rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (hc : p ≫ (X ↘ S) = π c ≫ Φ.algebraicRealizationStructureMap)
    (hd : q ≫ (X' ↘ S) = π d ≫ Φ.algebraicRealizationStructureMap)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hD' : (D'.comap q).support = (ι d).ker.support)
    [IsReduced D.subscheme] [IsReduced D'.subscheme]
    (heval :
      letI := IsIntegral.of_isIso f.inv
      f.hom.toRationalMap.comp (contractedXEvaluation b s c hΦ p) =
        g.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q))
    (hinj : Function.Injective (LineBundleClass.pullback p)) :
    D.comap f.hom = D'.comap g.hom ∧
      ∀ (a : LineBundleClass X) (a' : LineBundleClass X'),
        LineBundleClass.pullback f.hom a = LineBundleClass.pullback g.hom a' ↔
          (internalBlowupPicardMarking b s (center c) hΦ).symm
              (Additive.ofMul (LineBundleClass.pullback p a)) =
            (internalBlowupPicardMarking b s (center d) hΦ).symm
              (Additive.ofMul (LineBundleClass.pullback q a')) := by
  have := IsIntegral.of_isIso f.inv
  let e := f.symm ≪≫ g
  have hfg : f.hom ≫ e.hom = g.hom := by simp [e]
  have : e.hom.IsOver S := inferInstanceAs ((f.inv ≫ g.hom).IsOver S)
  have he : e.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q) =
      contractedXEvaluation b s c hΦ p := by
    apply Scheme.RationalMap.comp_left_injective f.hom.toRationalMap
    dsimp only
    simpa only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom, hfg] using heval.symm
  obtain ⟨_, ⟨_, _, _, hB, hPic⟩, _⟩ :=
    existsUnique_translation_of_comp_contractedXEvaluation_eq b s c d hΦ p q e
      hindex hc hd hD hD' he
  refine ⟨by rw [← hfg, Scheme.IdealSheafData.comap_comp, hB], fun a a' ↦ ?_⟩
  rw [← hfg, ← LineBundleClass.pullback_comp, ← LineBundleClass.pullbackEquiv_apply,
    ← LineBundleClass.pullbackEquiv_apply, (LineBundleClass.pullbackEquiv f).injective.eq_iff,
    ← hPic a']
  exact ((internalBlowupPicardMarking b s (center c) hΦ).symm.injective.comp
    (Additive.ofMul.injective.comp hinj)).eq_iff.symm

end TauCeti.Toric.Fan
