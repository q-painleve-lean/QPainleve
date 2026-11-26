/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Basic

import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Iso
import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Refinement
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Common ordered toric models of a specified pair isomorphism

The marked fibers of two toric presentations supply the endpoint projections
for [Lutz's resolved factorization](https://arxiv.org/pdf/2005.05010v3#page=68).
On a common nodal refinement their ordered models give the two original
X evaluations, with the target evaluation pulled back by the given pair isomorphism.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData Fan.LogarithmicProjection

namespace QPainleve.SignedClusterModularGroup

open MarkedSurface (surfaceIso)
open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "ToricBoundary[" Φ "," h "]" =>
  Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "R[" D "," π "]" => radical (comap D π)
local notation "E[" b "," s "]" =>
  chargeExchangeMatrix (LinearEquiv.toLinearMap (Module.Basis.detDualEquiv b)) (Fan.rayChargeMap s)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n] {L : Type}
  [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}

namespace ContractedToricFiber

variable {Φ : Fan i} [h₀ : Nonempty Φ.cones] {hΦ : Φ.IsRegular} {s : Fin r → Φ.Ray}
  [PrestableFamily (ToricBoundary[Φ,h₀] ↘ S)] {m : ℕ} [NeZero m]
  {γ : Type} {a : γ → (ToricBoundary[Φ,h₀] ↘ S).smoothLocus}
  {C : Scheme.NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ} {M : MarkedSurface ℂ n H X[r]}

local notation "model" => Fan.internalBlowupTower b s (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "q" => toBase (WithBoundary.toTower (Sigma.snd model))

private theorem exists_ordered_model
    (p : ContractedToricFiber b s hΦ C origin ι c M) (hc : Φ.IsComplete)
    {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [IsIntegral Y]
    (e : Y ≅ (model).1) (π : Y ⟶ M.surface) [IsModification π]
    (hp : p.projection = e.inv ≫ π) (hπ : π ≫ M.surface ↘ S = Y ↘ S) :
    let : IsIntegral M.surface := M.integral
    ∃ (A : Fan.LogarithmicProjection i R[D[M],π]) (W : OrderedToricModel A r),
      A.fan = Φ ∧ A.hom ≍ e.hom ≫ q ∧ IsModification A.hom ∧
      W.exchangeMatrix.matrix = E[b,s] ∧ W.xEvaluation = π.toRationalMap.comp M.evaluation := by
  let : IsIntegral M.surface := M.integral
  have he : e.hom ≫ p.projection = π := by simp only [hp, Iso.hom_inv_id_assoc]
  have hover : e.hom ≫ q ≫ Φ.algebraicRealizationStructureMap = Y ↘ S := by
    rw [← p.projection_over, ← Category.assoc, he, hπ]
  have hP : (D[M].comap π).support = ((model).2.boundaryι.ker.comap e.hom).support := by
    rw [← he, comap_comp, Scheme.IdealSheafData.support_comap (D[M].comap p.projection),
      p.support_comap, ← Scheme.IdealSheafData.support_comap]
  obtain ⟨A, W, hfan, hhom, hmod, hmat, hx⟩ :=
    Fan.exists_orderedToricModel_of_internalBlowupTower hc hΦ b s c e hover hP
  let := Fan.isIntegral_internalBlowupTower b s (fun j ↦ c (ofAdd (Pi.single j 1))) hΦ
  let := Fan.isModification_internalBlowupTower_toBase b s (fun j ↦ c (ofAdd (Pi.single j 1))) hΦ
  refine ⟨A, W, hfan, hhom, hmod, hmat, hx.trans ?_⟩
  calc
    _ = e.hom.toRationalMap.comp ((q).toRationalMap.comp (Φ.xEvaluation b s c)) := by
      simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom]
    _ = e.hom.toRationalMap.comp (p.projection.toRationalMap.comp M.evaluation) := by
      rw [p.evaluation_eq, Fan.comp_contractedXEvaluation]
    _ = _ := by
      simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom, he]

/-- A nodal extension of the specified contraction has an ordered endpoint
model over the original toric fan. The model gives the original exchange
matrix and the pullback of the marked surface's X evaluation. -/
theorem exists_ordered_model_on_nodal_extension
    (p : ContractedToricFiber b s hΦ C origin ι c M) (hc : Φ.IsComplete)
    (hD : D[M].IsEffectiveCartier)
    {k l : ℕ} {Y Z : Scheme} {T : BlowupTower M.surface k Y} {U : BlowupTower Y l Z}
    (hT : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) T)
    (hU : IsNodalBoundaryTower D[M] (M.surface ↘ S) T.toBase U)
    (e : Y ≅ (model).1) (hp : p.projection = e.inv ≫ T.toBase) :
    let : IsIntegral M.surface := M.integral
    let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
    let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    let : M.surface.IsProjectiveOver ℂ := M.projective
    let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
    let : Y.Over S := ⟨T.toBase ≫ M.surface ↘ S⟩
    let : Z.Over S := ⟨U.toBase ≫ Y ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension _
    let : SmoothOfRelativeDimension 2 (Z ↘ S) :=
      hU.isClosedPointTower.smoothOfRelativeDimension _
    let : IsIntegral Z := (hT.append (hU.congr (by rw [Category.comp_id])
      (by rw [Category.comp_id]))).isClosedPointTower.isIntegral (M.surface ↘ S)
    let : IsModification (U.toBase ≫ T.toBase) := by
      let : IsIntegral Y := hT.isClosedPointTower.isIntegral (M.surface ↘ S)
      let : IsModification T.toBase :=
        hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (M.surface ↘ S)
      let : IsModification U.toBase :=
        hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
      exact IsModification.comp _ _
    ∃ (A : Fan.LogarithmicProjection i R[D[M],U.toBase ≫ T.toBase])
      (W : OrderedToricModel A r),
      A.fan = Φ ∧ A.hom ≍ U.toBase ≫ e.hom ≫ q ∧ IsModification A.hom ∧
      W.exchangeMatrix = Fan.rayExchangeMatrix b s ∧
      W.xEvaluation = (U.toBase ≫ T.toBase).toRationalMap.comp M.evaluation := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let : Y.Over S := ⟨T.toBase ≫ M.surface ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension _
  let := hT.isClosedPointTower.isIntegral (M.surface ↘ S)
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsProper T.toBase := T.isProper_toBase
  let : IsProper (Y ↘ S) := inferInstanceAs (IsProper (T.toBase ≫ M.surface ↘ S))
  let : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  let := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (M.surface ↘ S)
  let P := R[D[M],T.toBase]
  obtain ⟨A, W, hfan, hhom, hmod, hmat, hxe⟩ :=
    p.exists_ordered_model hc e T.toBase hp rfl
  let := hmod
  have hu : IsNodalBoundaryTower P (Y ↘ S) (𝟙 Y) U :=
    hU.congr (by rw [Category.id_comp]; rfl) (by rw [comap_id, support_radical])
  obtain ⟨hCartier, hNodal⟩ := hT.radical_comap_toBase hD M.boundaryIdeal_nodal
  obtain ⟨Ψ, hΨ, J, d, hd, hE, _, hmat', hEval, _⟩ :=
    W.exists_refinement_on_nodalTower hCartier hNodal hu
  -- Both forms of the pole ideal are the reduced pullback to the same surface.
  have hrad : R[P,U.toBase] = R[D[M],U.toBase ≫ T.toBase] := by
    rw [radical_comap_radical, comap_comp]
  let := hU.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  let : Z.Over S := ⟨U.toBase ≫ Y ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.isClosedPointTower.smoothOfRelativeDimension _
  let := hU.isClosedPointTower.isIntegral (Y ↘ S)
  let : U.toBase.IsOver S := ⟨rfl⟩
  have hPole := hu.comap_eq_radical_mul_ramificationIdealSheaf_of_iso
    hCartier hNodal (Iso.refl Z) U.toBase (Category.id_comp _)
  let B := precomposeProjection
    ((Module.finrank_eq_card_basis W.basis).trans (Fintype.card_fin 2)) U.toBase hPole A
  let T' : OrderedToricModel B r :=
    ⟨Ψ, hΨ, J.trans W.subdivision, W.basis, J.liftRay ∘ W.rays, W.parameters, d, hd, hE⟩
  rw [← hrad]
  refine ⟨B, T', hfan, ?_, ?_, ?_, ?_⟩
  · cases hfan
    exact heq_of_eq (congrArg (U.toBase ≫ ·) (eq_of_heq hhom))
  · exact IsModification.comp U.toBase A.hom
  · exact hmat'.trans (SkewExchangeMatrix.ext (hmat.trans
      (Fan.rayExchangeMatrix_matrix _ _).symm))
  · rw [hEval, hxe, ← Scheme.RationalMap.comp_assoc]
    congr 1
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]

end ContractedToricFiber

namespace CompleteToricPresentation

variable {N' V' : Type} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V'] {i' : N' →+ V'}
  {b' : Module.Basis (Fin 2) ℤ N'} {r' : ℕ} {L' : Type} [AddCommGroup L']
  {H' : LinearMap.BilinForm ℤ L'} {γ γ' : Type}
  {M : MarkedSurface ℂ n H X[r]} {P : MarkedSurface ℂ n H' X[r']}

/-- Ordered toric models of the two projections on a common nodal refinement
of the source of a specified pair isomorphism. Each model retains its
presentation's exchange matrix and pulls back the corresponding evaluation. -/
@[ext]
structure CommonOrderedModels (Q : CompleteToricPresentation i b r L γ)
    (Q' : CompleteToricPresentation i' b' r' L' γ') (e : M.pair ≅ P.pair) where
  /-- The number of nodal blowups in the common refinement. -/
  length : ℕ
  /-- The surface on which both projections are defined. -/
  surface : Scheme
  /-- The blowup tower from the source surface to the common refinement. -/
  tower : BlowupTower M.surface length surface
  /-- The centers of the tower are nodes of the reduced boundary at each stage. -/
  isNodal : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) tower
  /-- The projection of the tower, used to index the reduced pullback. -/
  projection : surface ⟶ M.surface
  /-- The projection is the composite of the blowup maps. -/
  projection_eq_toBase : projection = tower.toBase
  /-- The structure morphism used by the two logarithmic projections. -/
  [over : surface.Over S]
  /-- The structure morphism is pulled back from the source. -/
  structureMap_eq : (surface ↘ S) = projection ≫ M.surface ↘ S
  /-- The common surface is smooth of relative dimension two. -/
  [smooth : SmoothOfRelativeDimension 2 (surface ↘ S)]
  /-- The common surface is integral. -/
  [integral : IsIntegral surface]
  /-- The projection to the source marked surface is a modification. -/
  [isModification_projection : IsModification projection]
  /-- The reduced pullback of the boundary is an effective Cartier divisor. -/
  isEffectiveCartier : R[D[M],projection].IsEffectiveCartier
  /-- The logarithmic projection to the source toric model. -/
  sourceProjection : Fan.LogarithmicProjection i R[D[M],projection]
  /-- The logarithmic projection to the target toric model. -/
  targetProjection : Fan.LogarithmicProjection i' R[D[M],projection]
  /-- The ordered toric model at the source endpoint. -/
  sourceModel : OrderedToricModel sourceProjection r
  /-- The ordered toric model at the target endpoint. -/
  targetModel : OrderedToricModel targetProjection r'
  /-- The source projection has the prescribed fan. -/
  sourceProjection_fan : sourceProjection.fan = Q.fan
  /-- The target projection has the prescribed fan. -/
  targetProjection_fan : targetProjection.fan = Q'.fan
  /-- The source projection is a modification. -/
  isModification_sourceProjection : IsModification sourceProjection.hom
  /-- The target projection is a modification. -/
  isModification_targetProjection : IsModification targetProjection.hom
  /-- The source model has the exchange matrix in the original source frame and labels. -/
  sourceModel_exchangeMatrix : sourceModel.exchangeMatrix = Fan.rayExchangeMatrix b Q.rays
  /-- The target model has the exchange matrix in the original target frame and labels. -/
  targetModel_exchangeMatrix : targetModel.exchangeMatrix = Fan.rayExchangeMatrix b' Q'.rays
  /-- The source evaluation is pulled back along the tower projection. -/
  sourceModel_xEvaluation : sourceModel.xEvaluation = projection.toRationalMap.comp M.evaluation
  /-- The target evaluation is pulled back along the tower projection and the
  specified isomorphism. -/
  targetModel_xEvaluation : targetModel.xEvaluation =
    projection.toRationalMap.comp ((surfaceIso e).hom.toRationalMap.comp P.evaluation)

namespace CommonOrderedModels

attribute [simp] sourceProjection_fan targetProjection_fan
  sourceModel_exchangeMatrix targetModel_exchangeMatrix
  sourceModel_xEvaluation targetModel_xEvaluation

end CommonOrderedModels

/-- Two marked nodal models related by a specified pair isomorphism give
ordered models of their two projections on one common nodal refinement. -/
theorem nonempty_commonOrderedModels_of_pair_iso
    (Q : CompleteToricPresentation i b r L γ)
    (Q' : CompleteToricPresentation i' b' r' L' γ')
    {c : Point Centers[r]} {d : Point Centers[r']}
    (hM : Q.HasNodalModel c M) (hP : Q'.HasNodalModel d P)
    (e : M.pair ≅ P.pair) (hD : D[M].IsEffectiveCartier) (hE : D[P].IsEffectiveCartier) :
    Nonempty (CommonOrderedModels Q Q' e) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  let := Q'.complete.nonempty_cones
  let := Q'.prestable
  let := Q'.neZero
  let : IsIntegral M.surface := M.integral
  let : IsIntegral P.surface := P.integral
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Smooth (P.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : P.surface.IsProjectiveOver ℂ := P.projective
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let : IsNoetherian P.surface := isNoetherian_of_finiteType (P.surface ↘ S)
  obtain ⟨p, Y, k, T, a, hT, ha⟩ := (Q.hasNodalModel_iff c M).mp hM
  obtain ⟨q, Z, l, U, a', hU, hb⟩ := (Q'.hasNodalModel_iff d P).mp hP
  have he := MarkedSurface.comap_boundaryIdeal_surfaceIso e
  -- Refine the two towers so their maps to the marked surfaces recover the specified isomorphism.
  obtain ⟨j, t, W, W', J, K, f, _, _, hJ, hK, hf⟩ :=
    hT.exists_common_refinement_of_pair_iso hU (surfaceIso e) (comp_over (surfaceIso e).hom S)
      (congrArg Scheme.IdealSheafData.support he)
  have hTJ : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) (T.append J) :=
    hT.append (hJ.congr (by rw [Category.comp_id]) (by rw [Category.comp_id]))
  have hUK : IsNodalBoundaryTower D[P] (P.surface ↘ S) (𝟙 _) (U.append K) :=
    hU.append (hK.congr (by rw [Category.comp_id]) (by rw [Category.comp_id]))
  let : Y.Over S := ⟨T.toBase ≫ M.surface ↘ S⟩
  let : Z.Over S := ⟨U.toBase ≫ P.surface ↘ S⟩
  let : W.Over S := ⟨J.toBase ≫ Y ↘ S⟩
  let : W'.Over S := ⟨K.toBase ≫ Z ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.isClosedPointTower.smoothOfRelativeDimension _
  have hW := hJ.isClosedPointTower.smoothOfRelativeDimension (Y ↘ S)
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hW
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.isClosedPointTower.smoothOfRelativeDimension _
  let : SmoothOfRelativeDimension 2 (W' ↘ S) := hK.isClosedPointTower.smoothOfRelativeDimension _
  let : IsIntegral W := hTJ.isClosedPointTower.isIntegral (M.surface ↘ S)
  let : IsIntegral Z := hU.isClosedPointTower.isIntegral (P.surface ↘ S)
  let : IsIntegral W' := hUK.isClosedPointTower.isIntegral (P.surface ↘ S)
  let π := J.toBase ≫ T.toBase
  have hπ : π = (T.append J).toBase := (toBase_append T J).symm
  have hOver : (W ↘ S) = π ≫ M.surface ↘ S := (Category.assoc ..).symm
  have hπmod : IsModification π := hπ.symm ▸
    hTJ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (M.surface ↘ S)
  have hf' : f.hom ≫ (K.toBase ≫ U.toBase) = π ≫ (surfaceIso e).hom :=
    hf.symm.trans (Category.assoc ..).symm
  have hfOver : f.hom ≫ K.toBase ≫ U.toBase ≫ P.surface ↘ S =
      J.toBase ≫ T.toBase ≫ M.surface ↘ S := by
    simpa only [π, Category.assoc, comp_over (surfaceIso e).hom S] using
      congrArg (· ≫ P.surface ↘ S) hf'
  let : f.hom.IsOver S := ⟨hfOver⟩
  let : IsModification (K.toBase ≫ U.toBase) := (toBase_append U K) ▸
    hUK.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (P.surface ↘ S)
  have hPole : R[D[P],K.toBase ≫ U.toBase].comap f.hom = R[D[M],π] := by
    rw [← radical_comap_of_isOpenImmersion, ← comap_comp, hf', comap_comp, he]
  -- Keep both prescribed projections and evaluations, transporting the target through the lift.
  obtain ⟨A, A', hAf, _, hmodA, hmatA, hEvalA⟩ :=
    p.exists_ordered_model_on_nodal_extension Q.complete hD hT hJ a ha
  obtain ⟨B, B', hBf, _, hmodB, hmatB, hEvalB⟩ :=
    q.exists_ordered_model_on_nodal_extension Q'.complete hE hU hK a' hb
  let := hmodB
  obtain ⟨C, C', hCf, _, hmodC, hmatC, hEvalC⟩ := B'.exists_precomposeIso f hPole
  have hR : R[D[M],π].IsEffectiveCartier := by
    rw [hπ]
    exact (hTJ.radical_comap_toBase hD M.boundaryIdeal_nodal).1
  let : IsModification π := hπmod
  refine ⟨{
    length := k + j, surface := W, tower := T.append J, isNodal := hTJ
    projection := π, projection_eq_toBase := hπ
    over := ⟨W ↘ S⟩, structureMap_eq := hOver, smooth := hW, integral := inferInstance
    isModification_projection := hπmod, isEffectiveCartier := hR
    sourceProjection := A, targetProjection := C, sourceModel := A', targetModel := C'
    sourceProjection_fan := hAf, targetProjection_fan := hCf.trans hBf
    isModification_sourceProjection := hmodA, isModification_targetProjection := hmodC
    sourceModel_exchangeMatrix := hmatA
    targetModel_exchangeMatrix := hmatC.trans hmatB
    sourceModel_xEvaluation := hEvalA, targetModel_xEvaluation := ?_ }⟩
  calc
    C'.xEvaluation = f.hom.toRationalMap.comp ((K.toBase ≫ U.toBase).toRationalMap.comp
        P.evaluation) := hEvalC.trans (congrArg (f.hom.toRationalMap.comp ·) hEvalB)
    _ = _ := by
      simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
        Scheme.Hom.toRationalMap_compHom, hf']

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
