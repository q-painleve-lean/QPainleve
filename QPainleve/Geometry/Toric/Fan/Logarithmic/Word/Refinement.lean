/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.Geometry.Toric.Fan.Picard.Subdivision
import QPainleve.Geometry.Toric.Fan.Subdivision.PrescribedTower

/-!
# Ordered endpoint models on a nodal refinement

A resolved path can require additional nodal blowups of its common source.
Each prescribed ordered toric model lifts to that same source. The original
labels and frame give the same exchange matrix, while the X evaluation and the
full Picard marking pull back under the nodal projection.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "s[" Δ "]" => Fan.algebraicRealizationStructureMap Δ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" M "]" => toBase (WithBoundary.toTower (Sigma.snd M))
local notation "boundary[" M "]" => WithBoundary.boundaryι (Sigma.snd M)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A : LogarithmicProjection i D} {m : ℕ}
  (U : OrderedToricModel A m)
  {n : ℕ} {W : Scheme} {T : QPainleve.BlowupTower Z n W}

local notation "model[" H "]" => Fan.internalBlowupTower
  (h₀ := IsSubdivision.nonempty_cones_of_nonempty H inferInstance)
  U.basis (IsSubdivision.liftRay H ∘ U.rays) U.parameters

omit [IsIntegral Z] in
private theorem exists_refined_tower
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 _) T) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (H : Ψ.IsSubdivision U.fan) (e : (model[H]).1 ≅ W),
      e.hom ≫ T.toBase ≫ U.hom = base[model[H]] ≫ π[H] ∧
      ((D.comap T.toBase).radical).comap e.hom = (boundary[model[H]]).ker := by
  have hs : U.iso.hom ≫ Z ↘ S = base[U.tower] ≫ s[U.fan] := by
    rw [← U.fan.algebraicRealization_over, ← comp_over U.hom S, ← Category.assoc,
      U.hom_def, Iso.hom_inv_id_assoc]
  let hnil : IsNodalBoundaryTower (boundary[U.tower]).ker (base[U.tower] ≫ s[U.fan])
      (𝟙 _) (.nil : QPainleve.BlowupTower U.tower.1 0 U.tower.1) := .nil
  obtain ⟨Y, L, a, hL, ha, hD⟩ := hnil.exists_append_of_iso hT U.iso
    (by simpa only [toBase_nil, Category.id_comp] using hs)
    (by rw [U.pole_eq, toBase_nil, comap_id])
  obtain ⟨Ψ, hΨ, H, d, hd, hB, -⟩ :=
    exists_subdivision_of_nodal_tower_on_internal_model U.basis U.rays U.parameters
      U.regular (U.subdivision.isComplete_iff.mpr A.isComplete) hL
  let e := d ≪≫ a
  have hproj : e.hom ≫ T.toBase ≫ U.hom = d.hom ≫ L.toBase ≫ base[U.tower] := by
    simp only [e, Iso.trans_hom, U.hom_def, ha, toBase_nil, Category.comp_id, Category.assoc]
  refine ⟨Ψ, hΨ, H, e, hproj.trans ((Category.assoc _ _ _).symm.trans hd.w), ?_⟩
  rw [Iso.trans_hom, comap_comp, ← hD]
  exact hB

variable [IsNoetherian Z]

local notation "over[" T "]" => OverClass.ofHom (toBase T ≫ Z ↘ S)
local notation "smooth[" h "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower h) (Z ↘ S)
local notation "integral[" h "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower h) (Z ↘ S)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis U.basis) (Fintype.card_fin 2)

/-- Lift a prescribed ordered model to a specified nodal refinement of its
resolving surface. The lifted model keeps the original frame and binomial
parameters. Its toric classes pull back along the fan subdivision, and the
coefficients of the total internal exceptional classes are preserved.
The exchange matrix is the same, and its fixed-center X evaluation is the
pullback of the original evaluation along the nodal tower. -/
theorem exists_refinement_on_nodalTower (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S))
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 _) T) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    letI : T.toBase.IsOver S := ⟨rfl⟩
    letI : IsModification T.toBase :=
      hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
    let A' := precomposeProjection rankTwo T.toBase
      (hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode (Iso.refl W) T.toBase
        (Category.id_comp _)) A
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (H : Ψ.IsSubdivision U.fan)
      (e : (model[H]).1 ≅ W)
      (he : e.hom ≫ A'.hom = base[model[H]] ≫ π[H.trans U.subdivision])
      (hE : ((D.comap T.toBase).radical).comap e.hom = (boundary[model[H]]).ker),
      let V : OrderedToricModel A' m :=
        ⟨Ψ, hΨ, H.trans U.subdivision, U.basis, H.liftRay ∘ U.rays, U.parameters, e, he, hE⟩
      T.toBase ≫ U.hom = V.hom ≫ π[H] ∧
      V.exchangeMatrix = U.exchangeMatrix ∧
      V.xEvaluation = T.toBase.toRationalMap.comp U.xEvaluation ∧
      ∀ (L : LineBundleClass X[U.fan]) (x : Fin m → ℤ),
        V.picardMarking (Additive.ofMul (pullback π[H] L), x) =
          Additive.ofMul (pullback T.toBase (U.picardMarking (Additive.ofMul L, x)).toMul) := by
  intro A'
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  obtain ⟨Ψ, hΨ, H, e, hproj, hE⟩ := U.exists_refined_tower hT
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty inferInstance
  have hcomp : A'.hom = T.toBase ≫ A.hom := (rfl)
  have he : e.hom ≫ A'.hom = base[model[H]] ≫ π[H.trans U.subdivision] := calc
    _ = (e.hom ≫ T.toBase ≫ U.hom) ≫ π[U.subdivision] := by
      rw [hcomp, ← U.hom_comp_subdivision]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [hproj, IsSubdivision.toFanHom_trans H U.subdivision, FanHom.algebraicMap_comp,
        Category.assoc]
  let V : OrderedToricModel A' m :=
    ⟨Ψ, hΨ, H.trans U.subdivision, U.basis, H.liftRay ∘ U.rays, U.parameters, e, he, hE⟩
  have hf : T.toBase ≫ U.hom = V.hom ≫ π[H] := by
    rw [V.hom_def, Category.assoc, ← hproj, Iso.inv_hom_id_assoc]
  have hmat : V.exchangeMatrix = U.exchangeMatrix := by
    apply QPainleve.Cluster.SkewExchangeMatrix.ext
    rw [V.exchangeMatrix_matrix, U.exchangeMatrix_matrix]
    simp only [V, IsSubdivision.rayChargeMap_liftRay]
  have hEval : V.xEvaluation = T.toBase.toRationalMap.comp U.xEvaluation := by
    let : IsDominant V.hom := V.refinedProjection.isDominant
    let x := U.fan.xEvaluation U.basis U.rays (centerCharacter U.parameters)
    have hx := H.comp_xEvaluation U.basis U.rays (centerCharacter U.parameters)
    have hmaps : T.toBase.toRationalMap.comp U.hom.toRationalMap =
        V.hom.toRationalMap.comp (π[H]).toRationalMap := by
      simp only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, hf]
    calc
      V.xEvaluation = V.hom.toRationalMap.comp ((π[H]).toRationalMap.comp x) :=
        V.xEvaluation_def.trans (congrArg (V.hom.toRationalMap.comp ·) hx.symm)
      _ = _ := by
        simp only [U.xEvaluation_def, ← Scheme.RationalMap.comp_assoc, hmaps]
        rfl
  have hPic (L : LineBundleClass X[U.fan]) (x : Fin m → ℤ) :
      V.picardMarking (Additive.ofMul (pullback π[H] L), x) =
        Additive.ofMul (pullback T.toBase (U.picardMarking (Additive.ofMul L, x)).toMul) := by
    have hg : (e.hom ≫ T.toBase ≫ U.iso.inv) ≫ base[U.tower] =
        base[model[H]] ≫ π[H] := by
      simpa only [Category.assoc, ← U.hom_def] using hproj
    have hmark := H.pullback_internalBlowupPicardMarking U.basis U.rays U.parameters
      hΨ U.regular _ hg L x
    rw [V.picardMarking_apply, U.picardMarking_apply]
    apply congrArg Additive.ofMul
    simp only [toMul_ofMul, V]
    rw [← hmark, pullback_comp, Iso.inv_hom_id_assoc, ← pullback_comp]
  exact ⟨Ψ, hΨ, H, e, he, hE, hf, hmat, hEval, hPic⟩

end TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel
