/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform
public import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.Reindex
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over
import QPainleve.Geometry.Toric.Fan.Boundary.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.SignedClusterModularGroup.Realization.Surface.Boundary
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

/-!
# Marked fibers without boundary contractions

When the Picard inclusion is an isometry onto the entire auxiliary lattice,
the internal blowup surface itself realizes the marked fiber. Its numbered
boundary is transported from the toric boundary, starting at the chosen
origin. Each numbered boundary class is the corresponding strict ray class
in the fixed Picard coordinates.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "param[" c "]" => (fun j ↦ χ[c] (ofAdd (Pi.single j 1)))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {b : Basis (Fin 2) ℤ N} {r : ℕ} {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation i b r L γ)

local instance instNonemptyInternalModelCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroInternalModelBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableInternalModelToricBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "X" => Q.fan.algebraicRealization
local instance : (X).IsProjectiveOver ℂ :=
  Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b

local instance : SmoothOfRelativeDimension 2 (X ↘ S) :=
  (Fan.algebraicRealization_over Q.fan).symm ▸
    ((finrank_eq_card_basis b).trans (Fintype.card_fin 2) ▸
      Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular)

local notation "Dtor" => Q.fan.boundaryIdeal Q.complete.nonempty_cones
local notation "Aux" => LinearMap.BilinForm.prod (Chow.intersectionBilinForm ℂ X)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

variable (c : GeometricRealization.Point Centers[r])

local notation "U" => Fan.internalBlowupTower b Q.rays param[c]
local notation "Y" => (U).1
local notation "T" => WithBoundary.toTower (Sigma.snd U)
local notation "D" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd U))
local notation "μ" => Fan.internalBlowupPicardMarking b Q.rays param[c] Q.regular
local notation "modelStructure" => toBase T ≫ (X ↘ S)

/-- The internal blowup model uses the composite of the ordered blowdown and the
toric surface's structure map to the complex base. -/
local instance : (Y).Over S := ⟨modelStructure⟩

local instance : IsIntegral Y := Fan.isIntegral_internalBlowupTower b Q.rays param[c] Q.regular

local instance : (Y).IsProjectiveOver ℂ := (T).isProjectiveOver ℂ

local instance : SmoothOfRelativeDimension 2 (Y ↘ S) :=
  (Fan.isClosedPointTower_internalBlowupTower b Q.rays param[c]).smoothOfRelativeDimension (X ↘ S)

private def internalModelMarking (e : H.IsometryEquiv (Aux)) :
    H.IsometryEquiv (Chow.intersectionBilinForm ℂ Y) := by
  let v : (Aux).IsometryEquiv (Chow.intersectionBilinForm ℂ Y) :=
    { toLinearEquiv := μ
      map_app' := by
        intro x y
        simpa only [picardMarking_apply, Fan.internalBlowupPicardMarking_apply,
          Chow.intersectionBilinForm_apply, LinearMap.BilinForm.prod_apply, LinearMap.neg_apply,
          LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, dotProductBilin_apply_apply, dotProduct,
          sub_eq_add_neg] using
            classIntersectionNumber_picardMarking ℂ
              (Fan.isClosedPointTower_internalBlowupTower b Q.rays param[c]) x y }
  exact e.trans v

private theorem internalModelMarking_apply (e : H.IsometryEquiv (Aux)) (x : L) :
    Q.internalModelMarking c e x = μ (e x) := rfl

private theorem isOver_internalBoundary :
    (U).2.boundaryι.IsOver S := by
  constructor
  rw [(Dtor).over_eq_subschemeι_comp]
  exact (U).2.boundaryι_toBase_assoc _

/-- The ordered internal blowup realizes a marked fiber when the marking identifies
its Picard lattice with all the toric and exceptional coordinates. Its numbered
boundary rays and classes are the strict rays in order from the presentation origin. -/
theorem exists_nodal_model_of_internalBlowup
    (e : H.IsometryEquiv (Aux)) (he : e.toLinearEquiv.toLinearMap = Q.inclusion) :
    ∃ (M : MarkedSurface ℂ Q.length H XTor[r])
      (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M),
      Q.HasNodalModel c M ∧ IsIso p.projection ∧
        ∃ hD : D[M].IsEffectiveCartier, ∀ j,
          p.numberedBoundaryRays hD j = Q.rayOrder (j + Q.origin) ∧
            M.boundaryClass hD j =
              e.symm (Q.fan.markedBoundaryMap Q.regular Q.rays
                (Pi.single (Q.rayOrder (j + Q.origin)) 1)) := by
  classical
  -- Identify the schematic image with the toric boundary and rotate its numbering.
  let : IsNoetherian Y := (T).isNoetherian
  let := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : (U).2.boundaryι.IsOver S := Q.isOver_internalBoundary c
  let a : (Dtor).subscheme ≅ (D).subscheme := asIso (U).2.boundaryι.toImage
  let : a.hom.IsOver S := inferInstanceAs ((U).2.boundaryι.toImage.IsOver S)
  have hboundary : a.hom ≫ (D).subschemeι = (U).2.boundaryι :=
    Scheme.Hom.toImage_imageι (U).2.boundaryι
  let : PrestableFamily ((D).subscheme ↘ S) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily) a.hom _).mp
      (by rw [comp_over]; exact Q.prestable)
  let marks : Empty → ((D).subscheme ↘ S).smoothLocus := Empty.elim
  let C := a.mapNodalCycleNumbering (Q.cycle.rotate Q.origin) (q := marks)
  let f := Fan.contractedXEvaluation b Q.rays χ[c] Q.regular (𝟙 Y)
  let M := MarkedSurface.ofBoundary D C (Q.internalModelMarking c e) f
  let : (Iso.refl (Dtor).subscheme).hom.IsOver S := by
    rw [Iso.refl_hom]
    infer_instance
  have hact : a.boundaryCycleAction Q.cycle C = DihedralGroup.r (-Q.origin) := by
    have hcomp := (Iso.refl (Dtor).subscheme).boundaryCycleAction_trans
      Q.cycle (Q.cycle.rotate Q.origin) a C
    simp only [Iso.refl_trans, C, a.boundaryCycleAction_mapNodalCycleNumbering, one_mul] at hcomp
    rw [hcomp]
    have h := (Iso.refl (Dtor).subscheme).boundaryCycleAction_symm
      (Q.cycle.rotate Q.origin) Q.cycle
    simpa only [Iso.refl_symm, ← Q.cycle.reindex_r,
      Q.cycle.boundaryCycleAction_refl_reindex, DihedralGroup.inv_r] using h
  have hgen (j : ZMod Q.length) :
      a.hom (Q.cycle.componentGenericPoint (j + Q.origin)) = C.componentGenericPoint j := by
    rw [a.apply_componentGenericPoint Q.cycle C, hact, DihedralGroup.cycleVertexPerm_r_apply,
      add_neg_cancel_right]
  -- The identity on the internal model gives the empty nodal tower.
  let p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M := {
    projection := 𝟙 Y
    modification := IsModification.of_isIso (𝟙 Y)
    boundary_over := inferInstanceAs (a.hom.IsOver S)
    projection_over := by
      -- Unfold the packaged surface to recover its chosen structure map.
      change 𝟙 Y ≫ modelStructure = _
      rw [Category.id_comp, Fan.algebraicRealization_over]
    support_comap := by
      have hker : D[M] = D := MarkedSurface.ofBoundary_ker ..
      -- Unfold the target surface for the identity pullback.
      exact congrArg IdealSheafData.support ((congrArg (fun J : (Y).IdealSheafData ↦
        J.comap (𝟙 Y)) hker).trans (comap_id D))
    boundaryMap := a.hom
    boundary_comp := by
      -- The packaged boundary map is the inclusion of the schematic image.
      change a.hom ≫ (D).subschemeι = (U).2.boundaryι ≫ (𝟙 Y)
      exact hboundary.trans (Category.comp_id _).symm
    orientedSubdivision := by
      -- Use the actual boundary and its transported numbering in the packaged surface.
      change a.hom.IsOrientedCycleSubdivision Q.cycle C
      exact a.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one _ _
        (by rw [hact, DihedralGroup.cycleOrientationSign_r])
    component_zero := by
      -- The numbering in the packaged surface is the transported numbering.
      change a.hom (Q.cycle.componentGenericPoint Q.origin) = C.componentGenericPoint 0
      simpa only [zero_add] using hgen 0
    marked_pullback := fun x ↦ by
      -- Identify the packaged Picard marking before simplifying the identity pullback.
      have hmark : M.picardMarking x = Q.internalModelMarking c e x :=
        MarkedSurface.ofBoundary_picardMarking ..
      exact (congrArg (fun u : Additive (LineBundleClass Y) ↦ (μ).symm
        (Additive.ofMul (LineBundleClass.pullback (𝟙 Y) u.toMul))) hmark).trans (by
          rw [LineBundleClass.pullback_id, ofMul_toMul, ← he]
          simp only [internalModelMarking_apply, LinearEquiv.symm_apply_apply,
            LinearEquiv.coe_coe, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv])
    evaluation_eq := MarkedSurface.ofBoundary_evaluation .. }
  have hN : Module.finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hD : (D).IsEffectiveCartier :=
    Fan.isEffectiveCartier_internalBlowupBoundary b Q.rays Q.regular param[c]
      (Q.fan.isEffectiveCartier_boundaryIdeal Q.regular Q.complete hN)
  have hker : D[M] = D := MarkedSurface.ofBoundary_ker ..
  have hM : D[M].IsEffectiveCartier := hker.symm ▸ hD
  refine ⟨M, p, (Q.hasNodalModel_iff c M).mpr ⟨p, Y, 0, .nil, Iso.refl _, ?_, by
    dsimp only [p]
    have hnil : (.nil : BlowupTower Y 0 Y).toBase = 𝟙 Y := toBase_nil
    exact ((Category.id_comp (𝟙 Y)).symm).trans
      (congrArg (fun g : Y ⟶ Y ↦ 𝟙 Y ≫ g) hnil.symm)⟩,
    inferInstanceAs (IsIso (𝟙 Y)), hM, fun j ↦ ⟨?_, ?_⟩⟩
  · exact .nil
  · rw [← Equiv.symm_apply_apply (Q.fan.boundaryNormalizationComponentEquiv Q.regular)
      (Q.rayOrder (j + Q.origin)), ← Q.component_eq]
    exact (p.numberedBoundaryRays_eq_iff hM j (j + Q.origin)).mpr (hgen j)
  · -- Compare the marked class with the strict ray prime on the same surface.
    apply M.picardMarking.injective
    rw [M.picardMarking_boundaryClass]
    have hprime : M.boundaryPrime hM j =
        (D).boundaryPrimeEmbedding (Fan.internalBlowupBoundaryPrimeEquiv Q.regular b
          Q.rays param[c] (Q.rayOrder (j + Q.origin))) := by
      apply Subtype.ext
      rw [M.coe_boundaryPrime, (D).coe_boundaryPrimeEmbedding,
        Fan.internalBlowupBoundaryPrime_val, ← Q.component_eq, ← Q.cycle.componentGenericPoint_def]
      -- Evaluate the image factorization on the corresponding generic point.
      change (D).subschemeι (C.componentGenericPoint j) = _
      rw [← hgen j, ← Scheme.Hom.comp_apply, hboundary]
    rw [hprime, MarkedSurface.ofBoundary_picardMarking]
    rw [internalModelMarking_apply, LinearMap.BilinForm.IsometryEquiv.apply_symm_apply]
    let z := Fan.internalBlowupBoundaryPrimeEquiv Q.regular b Q.rays param[c]
      (Q.rayOrder (j + Q.origin))
    have hz : (D).boundaryPrimeEmbedding z = ⟨z.val, (mem_boundaryPrimes.mp z.property).2⟩ :=
      Subtype.ext ((D).coe_boundaryPrimeEmbedding z)
    exact (congrArg (fun x : CodimensionOnePoint Y ↦ Additive.ofMul
      (LineBundleClass.primeDivisorClass x)) hz).trans (by
        rw [Fan.internalBlowupPicardMarking_apply]
        exact (Fan.picardHom_markedBoundaryMap_single_eq_primeDivisorClass
          Q.regular b Q.rays param[c] _).symm)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
