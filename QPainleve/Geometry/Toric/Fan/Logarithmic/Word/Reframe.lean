/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.Geometry.Toric.Fan.Boundary.Transport
import QPainleve.Geometry.Toric.Fan.Logarithmic.Reframe

/-!
# Transporting ordered toric models across lattices

An integral lattice equivalence carries an ordered model to its image fan in the
transported basis. It preserves the exchange matrix and the fixed-center X evaluation.
The ordered centers are transported by the lift of the toric isomorphism.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.BlowupTower
open QPainleve.CharacterTorus (centerCharacter)
open QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.LaurentRing
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel

local notation "S" => Spec (CommRingCat.of ℂ)

variable {N V N' V' : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A : LogarithmicProjection i D} {B : LogarithmicProjection i' D} {m : ℕ}

private theorem xEvaluation_eq_of_reframed_hom (U : OrderedToricModel A m)
    (W : OrderedToricModel B m) (f : FanEquiv U.fan W.fan)
    (hb : W.basis = U.basis.map f.latticeEquiv.toIntLinearEquiv)
    (ht : W.rays = f.rayEquiv ∘ U.rays) (hc : W.parameters = U.parameters)
    (hhom : U.hom ≫ f.toFanHom.algebraicMap = W.hom) :
    W.xEvaluation = U.xEvaluation := by
  let c := centerCharacter U.parameters
  have h := f.toFanHom.comp_xEvaluation U.basis W.basis U.rays W.rays id c c
    (fun _ ↦ rfl) (fun j ↦ by
      ext x
      simpa only [hb, ht, Function.comp_apply, FanEquiv.primitiveGenerator_rayEquiv,
        FanEquiv.toFanHom_latticeMap, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
        AddMonoidHom.coe_ofClass, id_eq, AddEquiv.coe_toIntLinearEquiv] using
        U.basis.detDualEquiv_map f.latticeEquiv.toIntLinearEquiv (U.rays j).primitiveGenerator x)
  have hid : CommRingCat.ofHom (AlgHom.id ℂ (LaurentRing ℂ (Fin m))).toRingHom = 𝟙 _ := rfl
  rw [rename_id, hid, Spec.map_id, Scheme.RationalMap.compHom_id] at h
  simpa only [W.xEvaluation_def, U.xEvaluation_def, hc, c, ← Scheme.RationalMap.comp_assoc,
    Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, hhom] using
    congrArg (U.hom.toRationalMap.comp ·) h

/-- An integral equivalence transports the ordered model to the new lattice.
The comparison commutes with the refined projections and preserves both seed
data and evaluation in the original order of labels. -/
theorem exists_reframe_of_latticeEquiv (U : OrderedToricModel A m)
    (hi' : IsIntegralLattice i') (e : N ≃+ N') :
    ∃ (B : LogarithmicProjection i' D) (W : OrderedToricModel B m)
      (f : FanEquiv U.fan W.fan),
      f.latticeEquiv = e ∧ W.basis = U.basis.map f.latticeEquiv.toIntLinearEquiv ∧
      W.rays = f.rayEquiv ∘ U.rays ∧ W.parameters = U.parameters ∧
      U.hom ≫ f.toFanHom.algebraicMap = W.hom ∧ IsModification B.hom ∧
      W.exchangeMatrix = U.exchangeMatrix ∧ W.xEvaluation = U.xEvaluation := by
  let f := U.fan.mapEquivIso hi' e
  have rank := (finrank_eq_card_basis U.basis).trans (Fintype.card_fin 2)
  have hF := U.refinedProjection.reframe_fan f rank
  have hB := U.refinedProjection.reframe_hom f rank
  have hmod := (U.refinedProjection.isModification_reframe_iff f rank).mpr inferInstance
  generalize U.refinedProjection.reframe f rank = B at hF hB hmod
  obtain ⟨Ψ, hΨ, hc, p, hp, hd, hPole⟩ := B
  dsimp only at hF hB
  subst Ψ
  let B : LogarithmicProjection i' D := ⟨_, hΨ, hc, p, hp, hd, hPole⟩
  let b := U.basis.map f.latticeEquiv.toIntLinearEquiv
  let t := f.rayEquiv ∘ U.rays
  let : Nonempty B.fan.cones := B.isComplete.nonempty_cones
  let T := B.fan.internalBlowupTower b t U.parameters
  obtain ⟨g, ⟨hg, hgB⟩, -⟩ := f.existsUnique_isLift_internalBlowupTower U.basis b
    (U.basis.detDualEquiv_map f.latticeEquiv.toIntLinearEquiv) U.rays U.parameters U.regular
  let w : T.1 ≅ Z := g.symm ≪≫ U.iso
  have hB : B.hom = U.hom ≫ f.toFanHom.algebraicMap := eq_of_heq hB
  have hbase : g.hom ≫ T.2.toTower.toBase =
      U.tower.2.toTower.toBase ≫ f.toFanHom.algebraicMap := hg.hom_toBase
  have hw : w.hom ≫ B.hom = T.2.toTower.toBase := by
    exact (cancel_epi g.hom).mp (by
      simpa only [w, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, hB, U.hom_def,
        Category.assoc] using hbase.symm)
  have pole : D.comap w.hom = T.2.boundaryι.ker := by
    have hker : T.2.boundaryι.ker.comap g.hom = U.tower.2.boundaryι.ker := by
      rw [← Scheme.Hom.ker_comp_of_isIso (f := (f.boundaryIso _ _).hom) (g := T.2.boundaryι),
        ← hgB, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
    simp only [w, Iso.trans_hom, Iso.symm_hom]
    rw [comap_comp, U.pole_eq, ← hker, ← comap_comp, Iso.inv_hom_id, comap_id]
  let W : OrderedToricModel B m :=
    ⟨B.fan, B.isRegular, IsSubdivision.refl B.fan, b, t, U.parameters, w,
      by simpa only [IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, Category.comp_id]
        using hw, pole⟩
  have hhom : U.hom ≫ f.toFanHom.algebraicMap = W.hom := by
    simpa only [W, IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, Category.comp_id]
      using (hB.symm.trans W.hom_comp_subdivision.symm)
  refine ⟨B, W, f, Fan.mapEquivIso_latticeEquiv _ _ _, rfl, rfl, rfl, hhom, hmod, ?_,
    U.xEvaluation_eq_of_reframed_hom W f rfl rfl rfl hhom⟩
  apply SkewExchangeMatrix.ext
  rw [W.exchangeMatrix_matrix, U.exchangeMatrix_matrix]
  ext j k
  simpa only [chargeExchangeMatrix_apply, rayChargeMap_single, W, t, b, Function.comp_apply,
    FanEquiv.primitiveGenerator_rayEquiv, AddEquiv.coe_toIntLinearEquiv, LinearEquiv.coe_coe] using
    U.basis.detDualEquiv_map f.latticeEquiv.toIntLinearEquiv
      (U.rays j).primitiveGenerator (U.rays k).primitiveGenerator

end TauCeti.Toric.Fan.LogarithmicProjection.OrderedToricModel
