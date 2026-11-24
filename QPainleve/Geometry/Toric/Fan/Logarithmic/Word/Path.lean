/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Star

import QPainleve.Geometry.Toric.Fan.Logarithmic.Evaluation
import QPainleve.Geometry.Toric.Fan.Mutation.ResolvedEvaluation

/-!
# Cluster words along resolved Sarkisov paths

The fixed-center X evaluations along the links in the factorization of
[Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68) compose on their
common resolving surface. Changing from a model's frame to the frame of a link
may require a coordinate inversion.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open QPainleve QPainleve.Cluster QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "base[" T "]" => QPainleve.BlowupTower.toBase (WithBoundary.toTower (Sigma.snd T))

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [IsIntegral Z]
  {D : Z.IdealSheafData} {A B : LogarithmicProjection i D} {m : ℕ}

namespace OrderedToricModel

private theorem exists_compOfDefined_nil (U : OrderedToricModel A m) :
    let w : Word U.exchangeMatrix U.exchangeMatrix := .nil
    ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = U.xEvaluation := by
  simpa only [Quiver.Path.xRationalMap_nil, Scheme.RationalMap.compHom_id] using
    U.xEvaluation.compOfDefined_toRationalMap (𝟙 _)

/-- Successive words carrying one fixed-center evaluation to the next compose
at the generic point of the same resolving surface. -/
theorem exists_compOfDefined_word_comp {C : LogarithmicProjection i D}
    (U : OrderedToricModel A m) (M : OrderedToricModel B m) (W : OrderedToricModel C m)
    (u : Word U.exchangeMatrix M.exchangeMatrix) (v : Word M.exchangeMatrix W.exchangeMatrix)
    (h₀ : ∃ h, U.xEvaluation.compOfDefined (u.xRationalMap ℂ) h = M.xEvaluation)
    (h₁ : ∃ h, M.xEvaluation.compOfDefined (v.xRationalMap ℂ) h = W.xEvaluation) :
    ∃ h, U.xEvaluation.compOfDefined ((u.comp v).xRationalMap ℂ) h = W.xEvaluation := by
  obtain ⟨hu, h₀⟩ := h₀
  obtain ⟨hv, h₁⟩ := h₁
  obtain ⟨h, he⟩ := U.xEvaluation.compOfDefined_comp (u.xRationalMap ℂ) (v.xRationalMap ℂ)
    hu (h₀.symm ▸ hv)
  refine ⟨(Quiver.Path.xRationalMap_comp ℂ u v).symm ▸ h, ?_⟩
  simpa only [Quiver.Path.xRationalMap_comp, ← he, h₀] using h₁

omit [IsIntegral Z] in
private theorem exists_iso_of_tower_eq (U : OrderedToricModel A m)
    (b : Basis (Fin 2) ℤ N) (c : Fin m → ℂˣ)
    (h : U.fan.internalBlowupTower b U.rays c = U.tower) :
    ∃ e : (U.fan.internalBlowupTower b U.rays c).1 ≅ Z,
      e.hom ≫ A.hom = base[U.fan.internalBlowupTower b U.rays c] ≫ π[U.subdivision] ∧
        D.comap e.hom = (U.fan.internalBlowupTower b U.rays c).2.boundaryι.ker ∧
        e.inv ≫ base[U.fan.internalBlowupTower b U.rays c] = U.hom ∧
        ∀ a, Additive.ofMul (LineBundleClass.pullback e.inv
          ((U.fan.internalBlowupTower b U.rays c).2.toTower.picardHom a).toMul) =
          U.picardMarking a := by
  simp only [picardMarking_apply, Fan.internalBlowupPicardMarking_apply]
  exact h.symm ▸ Exists.intro U.iso ⟨U.hom_eq, U.pole_eq, U.hom_def.symm, fun _ ↦ rfl⟩

private theorem exists_reframe_of_det_eq (U : OrderedToricModel A m) (b : Basis (Fin 2) ℤ N)
    (hb : b.det = U.basis.det) :
    ∃ W : OrderedToricModel A m, W.basis = b ∧ W.refinedProjection = U.refinedProjection ∧
      W.picardMarking ≍ U.picardMarking ∧ W.exchangeMatrix = U.exchangeMatrix ∧
      W.xEvaluation = U.xEvaluation := by
  have hdet (v : N) : b.detDualEquiv v = U.basis.detDualEquiv v := by
    ext y
    simp only [Basis.detDualEquiv_apply, hb]
  have hTower : U.fan.internalBlowupTower b U.rays U.parameters = U.tower := by
    simp only [Fan.internalBlowupTower_eq_alongBoundary]
    congr 1
    funext j
    apply Subtype.ext
    simp only [Fan.Ray.internalCenter_val]
    congr 2
    exact congrArg LinearMap.toAddMonoidHom (hdet _)
  obtain ⟨e, he, hP, hh, hm⟩ := U.exists_iso_of_tower_eq b U.parameters hTower
  let W : OrderedToricModel A m :=
    ⟨U.fan, U.regular, U.subdivision, b, U.rays, U.parameters, e, he, hP⟩
  have hhom : W.hom = U.hom := W.hom_def.trans hh
  have href : W.refinedProjection = U.refinedProjection :=
    LogarithmicProjection.ext rfl (heq_of_eq hhom)
  refine ⟨W, rfl, href, heq_of_eq (LinearEquiv.ext fun a ↦ ?_), SkewExchangeMatrix.ext ?_, ?_⟩
  · simpa only [W, picardMarking_apply, Fan.internalBlowupPicardMarking_apply] using hm a
  · ext j k
    simp only [exchangeMatrix_matrix, W, chargeExchangeMatrix_apply, rayChargeMap_single,
      LinearEquiv.coe_coe, hdet]
  · simp only [xEvaluation_def, hhom]
    congr 1
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    simp only [Fan.fromFunctionField_xEvaluation]
    congr 2
    apply congrArg AlgHom.toRingHom
    apply LaurentRing.algHom_ext
    intro j
    simp only [Fan.xEval_X, W, hdet]

private theorem exists_reframe_swap (U : OrderedToricModel A m) :
    ∃ W : OrderedToricModel A m, W.basis = U.basis.reindex (Equiv.swap 0 1) ∧
      W.refinedProjection = U.refinedProjection ∧ W.picardMarking ≍ U.picardMarking ∧
      W.exchangeMatrix = -U.exchangeMatrix ∧
      W.xEvaluation = U.xEvaluation.compHom
        (CharacterTorus.map ℂ (AddEquiv.neg (Fin m →₀ ℤ)).toAddMonoidHom) := by
  let b := U.basis.reindex (Equiv.swap 0 1)
  have hTower : U.fan.internalBlowupTower b U.rays U.parameters⁻¹ = U.tower :=
    Fan.internalBlowupTower_reindex_swap _ _ _
  obtain ⟨e, he, hP, hh, hm⟩ := U.exists_iso_of_tower_eq b U.parameters⁻¹ hTower
  let W : OrderedToricModel A m :=
    ⟨U.fan, U.regular, U.subdivision, b, U.rays, U.parameters⁻¹, e, he, hP⟩
  have hhom : W.hom = U.hom := W.hom_def.trans hh
  have href : W.refinedProjection = U.refinedProjection :=
    LogarithmicProjection.ext rfl (heq_of_eq hhom)
  refine ⟨W, rfl, href, heq_of_eq (LinearEquiv.ext fun a ↦ ?_), SkewExchangeMatrix.ext ?_, ?_⟩
  · simpa only [W, picardMarking_apply, Fan.internalBlowupPicardMarking_apply] using hm a
  · simp only [exchangeMatrix_matrix, W, b, Fan.chargeExchangeMatrix_reindex_swap,
      SkewExchangeMatrix.neg_matrix]
  have hc : centerCharacter U.parameters⁻¹ = (centerCharacter U.parameters)⁻¹ := by
    ext x
    simp [centerCharacter, map_inv]
  simp only [xEvaluation_def, hhom]
  simp only [W, b, hc, Fan.xEvaluation_reindex_swap, Scheme.RationalMap.comp_compHom]

/-- Express an ordered model in the specified frame, keeping its refined projection and marking.
The word between the two X evaluations implements the determinant sign of the frame change. -/
theorem exists_word_reframe (U : OrderedToricModel A m) (b : Basis (Fin 2) ℤ N) :
    ∃ (W : OrderedToricModel A m) (w : Word U.exchangeMatrix W.exchangeMatrix),
      W.basis = b ∧ W.refinedProjection = U.refinedProjection ∧ W.picardMarking ≍ U.picardMarking ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  have hb := b.det.eq_smul_basis_det U.basis
  rcases Int.isUnit_iff.mp (b.isUnit_det U.basis) with h | h
  · rw [h, one_smul] at hb
    obtain ⟨W, hW, href, hm, hB, hEval⟩ := U.exists_reframe_of_det_eq b hb
    refine ⟨W, hB.symm ▸ Quiver.Path.nil, hW, href, hm, ?_⟩
    generalize W.exchangeMatrix = C at hB ⊢
    subst C
    simpa only [hEval] using
      U.exists_compOfDefined_nil
  · obtain ⟨M, hM, hMref, hMm, hB, hEval⟩ := U.exists_reframe_swap
    have hb' : b.det = M.basis.det := by
      rw [hb, h, hM]
      apply AlternatingMap.ext
      intro x
      simpa only [neg_one_smul, neg_apply, Basis.det_reindex] using
        (U.basis.det.map_swap x (by decide : (0 : Fin 2) ≠ 1)).symm
    obtain ⟨W, hW, href, hm, hB', hEval'⟩ := M.exists_reframe_of_det_eq b hb'
    have hEnd := hB'.trans (hB.trans (Generator.target_invert U.exchangeMatrix).symm)
    let f := CharacterTorus.map ℂ (AddEquiv.neg (Fin m →₀ ℤ)).toAddMonoidHom
    let w := (Generator.invert.toStep U.exchangeMatrix).toPath
    have hw : w.xRationalMap ℂ = f.toRationalMap :=
      Quiver.Path.xRationalMap_invert ℂ U.exchangeMatrix
    obtain ⟨hd, he⟩ := U.xEvaluation.compOfDefined_toRationalMap f
    refine ⟨W, hEnd.symm ▸ w, hW, href.trans hMref, hm.trans hMm, ?_⟩
    -- Only the target exchange matrix is transported.
    generalize W.exchangeMatrix = C at hEnd ⊢
    subst C
    simp only [hw, hEval', hEval]
    exact ⟨hd, he⟩

end OrderedToricModel

local notation "μ[" Δ "," b "," ρ "," c "," h "]" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Δ b (c : ℂ)
    (Fan.Ray.primitiveGenerator_ne_zero ρ) (Fan.Ray.hull_primitiveGenerator_mem ρ) h)
local notation "M[" Δ "," b "," ρ "," h "]" =>
  Fan.mutationFan Δ b (Fan.Ray.primitiveGenerator_ne_zero ρ)
    (Fan.Ray.hull_primitiveGenerator_mem ρ) h

private theorem exists_word_of_mutation_in_frame (U : OrderedToricModel A m)
    (b : Basis (Fin 2) ℤ N) (hb : U.basis = b)
    (ρ : A.fan.Ray) (c : ℂˣ) (opp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ A.fan.cones)
    (hFan : B.fan = M[A.fan,b,ρ,opp])
    (hMap : A.hom.toRationalMap.comp μ[A.fan,b,ρ,c,opp] =
      (cast (congrArg (fun Φ : Fan i ↦ Z ⟶ X[Φ]) hFan) B.hom).toRationalMap) :
    ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix),
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  subst b
  have hModel := U.exists_model_of_mutation_in_basis ρ opp c hFan hMap
  extract_lets at hModel
  obtain ⟨n, hm, k, hModel⟩ := hModel
  extract_lets at hModel
  obtain ⟨hk, hc, e, he, hp, hStep⟩ := hModel
  extract_lets W at hStep
  obtain ⟨step, hStep⟩ := hStep
  subst m
  have hrat := step.comp_rationalMap
  rw [hStep] at hrat
  obtain ⟨hMatrix, -, hEval⟩ := U.fan.compare_ordered_mutation U.basis
    (U.rays ∘ finCongr rfl) (U.parameters ∘ finCongr rfl) k _ _ c hk.symm hc.symm
    U.hom W.hom hrat
  let w := (((Generator.mutate k).toStep U.exchangeMatrix).toPath).comp
    (((Generator.permute ((finSuccEquiv _).trans (finSuccEquiv' k).symm)).toStep _).toPath)
  have hw : W.exchangeMatrix = _ := hMatrix
  refine ⟨W, hw.symm ▸ w, ⟨step⟩, ?_⟩
  -- Transport only the terminal type of the word.
  generalize W.exchangeMatrix = E at hw ⊢
  subst E
  simp only [OrderedToricModel.xEvaluation_def]
  exact hEval

private theorem exists_word_of_star_step [Z.IsProjectiveOver ℂ]
    (U : OrderedToricModel A m) (e : StarStep A B) :
    ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix),
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  let p := @Quiver.Hom.toPath _ instQuiver A B e
  obtain ⟨K, hK, hp⟩ := exists_word_of_resolved_star_path p U
  let W : OrderedToricModel B m :=
    ⟨U.fan, U.regular, K, U.basis, U.rays, U.parameters, U.iso, hK, U.pole_eq⟩
  let f : X[U.fan] ⟶ X[U.fan] := 𝟙 _
  refine ⟨W, .nil, ⟨⟨f.toRationalMap, ?_, ?_⟩⟩, hp.2.2.2.2⟩
  · simpa only [f, FanEquiv.toFanHom_refl, FanHom.algebraicMap_id, Fan.torusTranslation_one,
      Iso.refl_hom, Category.id_comp] using
        IsSarkisovLink.toricIso (FanEquiv.refl U.fan) 1
  · simp only [f, Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.compHom_id,
      U.hom_def, W.hom_def]
    exact (rfl)

private theorem exists_word_of_toric_iso (U : OrderedToricModel A m)
    (f : FanEquiv A.fan B.fan) (χ : Multiplicative (N →+ ℤ) →* ℂˣ)
    (hf : A.hom.toRationalMap.comp
      (f.toFanHom.algebraicMap ≫ (B.fan.torusTranslation χ).hom).toRationalMap =
        B.hom.toRationalMap) :
    ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix),
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  have hModel := U.exists_model_of_iso f χ hf
  extract_lets Θ F K b s c at hModel
  obtain ⟨e, he, hPole, hModel⟩ := hModel
  extract_lets W at hModel
  obtain ⟨hmap, hStep⟩ := hModel
  let : Nonempty Θ.cones := K.nonempty_cones_of_nonempty B.isComplete.nonempty_cones
  have hdet := U.basis.detDualEquiv_map F.latticeEquiv.toIntLinearEquiv
  have hEval := F.comp_xEvaluation_of_toric_iso U.basis b U.rays s id
    (centerCharacter U.parameters) (centerCharacter c) χ (fun _ ↦ rfl) hdet
    (fun j ↦ by simp [c, centerCharacter, Finsupp.linearEquivFunOnFinite_symm_single])
  have hEq : W.xEvaluation = U.xEvaluation := by
    simp only [OrderedToricModel.xEvaluation_def, ← hmap,
      ← Scheme.Hom.toRationalMap_compHom, ← Scheme.RationalMap.comp_toRationalMap,
      Scheme.RationalMap.comp_assoc]
    congr 1
    simpa only [LaurentRing.rename_id, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom,
      CommRingCat.ofHom_id, Spec.map_id, Scheme.RationalMap.compHom_id, W, Θ] using hEval
  have hB : W.exchangeMatrix = U.exchangeMatrix := by
    apply SkewExchangeMatrix.ext
    ext j k
    simp only [OrderedToricModel.exchangeMatrix_matrix, chargeExchangeMatrix_apply,
      rayChargeMap_single, LinearEquiv.coe_coe, W, s, Function.comp_apply,
      FanEquiv.primitiveGenerator_rayEquiv]
    exact hdet _ _
  refine ⟨W, hB.symm ▸ Quiver.Path.nil, hStep, ?_⟩
  generalize W.exchangeMatrix = E at hB ⊢
  subst E
  simpa only [hEq] using U.exists_compOfDefined_nil

/-- A specified resolved Sarkisov link transports an ordered model and supplies
a typed X word in the source and terminal labelings. The induced link on the
refined fans is resolved on the same surface, and the word carries the source
X evaluation to the target evaluation at the generic point. -/
theorem SarkisovStep.exists_word [Z.IsProjectiveOver ℂ] (e : SarkisovStep A B)
    (U : OrderedToricModel A m) :
    ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix),
      Nonempty (SarkisovStep U.refinedProjection W.refinedProjection) ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  rcases e with ⟨f, hf, he⟩
  cases A
  cases B
  cases hf with
  | blowup H =>
    apply exists_word_of_star_step U (.blowup H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_algebraicRealization
    apply Scheme.Hom.toRationalMap_injective
    have hh := congrArg (fun g ↦ g.compHom π[H.isSubdivision]) he
    rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
      H.isSubdivision.toRationalMap_algebraicMap, denseTorusPartialIso_toRationalMap_comp,
      denseTorusPartialIso_self_toRationalMap, Scheme.RationalMap.comp_id,
      Scheme.Hom.toRationalMap_compHom] at hh
    exact hh.symm
  | blowdown H =>
    apply exists_word_of_star_step U (.blowdown H ?_)
    let (F : Fan i) : X[F].IsSeparated := F.isSeparated_algebraicRealization
    apply Scheme.Hom.toRationalMap_injective
    rwa [← H.isSubdivision.toRationalMap_algebraicMap, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom] at he
  | mutation b ρ c hOpp =>
    rename_i hReg hComplete r hOver hDom hPole
    let C : LogarithmicProjection i D := ⟨_, hReg, hComplete, r, hOver, hDom, hPole⟩
    obtain ⟨U', u, hb, hRef, -, hu⟩ := U.exists_word_reframe b
    obtain ⟨W, w, hStep, hw⟩ := exists_word_of_mutation_in_frame (B := C) U' b hb ρ c hOpp rfl he
    exact ⟨W, u.comp w, hRef ▸ hStep, U.exists_compOfDefined_word_comp U' W u w hu hw⟩
  | toricIso f χ =>
    exact exists_word_of_toric_iso U f χ he

/-- Read a specified resolved Sarkisov path as a typed cluster word starting
from a supplied ordered model. Its evaluation is defined at the generic value
on the common resolving surface and equals the evaluation of the transported
terminal model. The path on the refined fans forgets to the specified path,
and its composite commutes with the endpoint subdivisions. -/
theorem exists_word_of_resolved_sarkisov_path [Z.IsProjectiveOver ℂ] (p : SarkisovPath A B)
    (U : OrderedToricModel A m) :
    ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix)
      (q : @Quiver.Path _ (presentationQuiver m) ⟨A, U⟩ ⟨B, W⟩),
      (forgetPresentation m).mapPath q = p ∧
        π[U.subdivision].toRationalMap.comp p.rationalMap =
          (SarkisovPath.rationalMap ((refinePresentation m).mapPath q)).comp
            π[W.subdivision].toRationalMap ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
  have hLift : ∃ (W : OrderedToricModel B m) (w : Word U.exchangeMatrix W.exchangeMatrix)
      (q : @Quiver.Path _ (presentationQuiver m) ⟨A, U⟩ ⟨B, W⟩),
      (forgetPresentation m).mapPath q = p ∧
        ∃ h, U.xEvaluation.compOfDefined (w.xRationalMap ℂ) h = W.xEvaluation := by
    induction p with
    | nil => exact ⟨U, .nil, .nil, rfl, U.exists_compOfDefined_nil⟩
    | cons p e ih =>
      obtain ⟨M, u, q, rfl, hu⟩ := ih
      obtain ⟨W, v, ⟨f⟩, hv⟩ := SarkisovStep.exists_word e M
      exact ⟨W, u.comp v, q.cons (e, f), rfl, U.exists_compOfDefined_word_comp M W u v hu hv⟩
  obtain ⟨W, w, q, hq, h⟩ := hLift
  exact ⟨W, w, q, hq, p.subdivision_comp_rationalMap U W _, h⟩

end TauCeti.Toric.Fan.LogarithmicProjection
