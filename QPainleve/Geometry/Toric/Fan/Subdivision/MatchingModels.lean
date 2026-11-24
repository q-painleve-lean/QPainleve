/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction
public import QPainleve.Geometry.Toric.Fan.Evaluation.Contraction
public import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Picard.Subdivision
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField

/-!
# Comparing contracted toric models on a common refinement

The ordered internal models of two matching toric presentations have a common
nodal refinement. The endpoint isomorphism downstairs preserves the boundary and
the fixed-center X evaluation. In Picard coordinates its pullback is characterized
by equality after transporting the toric classes to the common fan and retaining
the coefficients of all total internal exceptional classes.
The comparison uses `IsSubdivision.pullback_internalBlowupPicardMarking` on the
common model and injectivity of Picard pullback along the nodal tower.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Ω : Fan i}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones] [Nonempty Ω.cones]
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}

local notation "model" => internalBlowupTower b

private theorem evaluation_eq_on_common_subdivision
    (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator)
    (c : Multiplicative (Fin n → ℤ) →* ℂˣ) {W : Scheme} [IsIntegral W]
    (a : W ⟶ Ω.algebraicRealization) [IsDominant a] :
    (a ≫ hΩΦ.toFanHom.algebraicMap).toRationalMap.comp (Φ.xEvaluation b ρ c) =
      (a ≫ hΩΨ.toFanHom.algebraicMap).toRationalMap.comp (Ψ.xEvaluation b τ c) := by
  open Scheme.RationalMap in
    simp only [← Scheme.Hom.toRationalMap_compHom, ← comp_toRationalMap, comp_assoc,
      hΩΦ.comp_xEvaluation, hΩΨ.comp_xEvaluation,
      hΩΦ.liftRay_comp_eq_of_primitiveGenerator_eq hΩΨ ρ τ hρτ]

private theorem pullback_coordinates (h : Ω.IsSubdivision Φ)
    (hΩ : Ω.IsRegular) (hΦ : Φ.IsRegular) (ρ : Fin n → Φ.Ray) {τ : Fin n → Ω.Ray}
    (hτ : h.liftRay ∘ ρ = τ) (c : Fin n → ℂˣ)
    (g : (model τ c).1 ⟶ (model ρ c).1)
    (hg : g ≫ (model ρ c).2.toTower.toBase =
      (model τ c).2.toTower.toBase ≫ h.toFanHom.algebraicMap)
    (L : LineBundleClass (model ρ c).1) :
    let a := (internalBlowupPicardMarking b ρ c hΦ).symm (Additive.ofMul L)
    Additive.ofMul (pullback g L) = internalBlowupPicardMarking b τ c hΩ
      (Additive.ofMul (pullback h.toFanHom.algebraicMap a.1.toMul), a.2) := by
  subst τ
  obtain ⟨⟨A, m⟩, hL⟩ := (internalBlowupPicardMarking b ρ c hΦ).surjective (Additive.ofMul L)
  have h : L = (internalBlowupPicardMarking b ρ c hΦ (A, m)).toMul :=
    (Additive.ofMul.injective (hL.trans (ofMul_toMul _).symm)).symm
  subst L
  simpa only [LinearEquiv.symm_apply_apply, toMul_ofMul, ofMul_toMul] using
    congrArg Additive.ofMul (h.pullback_internalBlowupPicardMarking b ρ c hΩ hΦ g hg A.toMul m)

local notation "centers(" c ")" => (fun j ↦ c (ofAdd (Pi.single j 1)))

private theorem comp_contractedXEvaluation_of_common_subdivision
    {X X' : Scheme} [IsIntegral X] [IsIntegral X']
    (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator)
    {p : (model ρ centers(c)).1 ⟶ X} {q : (model τ centers(c)).1 ⟶ X'}
    [IsModification p] [IsModification q]
    (u : (model (hΩΦ.liftRay ∘ ρ) centers(c)).1 ⟶ (model ρ centers(c)).1)
    (v : (model (hΩΦ.liftRay ∘ ρ) centers(c)).1 ⟶ (model τ centers(c)).1)
    [IsDominant u] [IsDominant v]
    (hu : u ≫ (model ρ centers(c)).2.toTower.toBase =
      (model (hΩΦ.liftRay ∘ ρ) centers(c)).2.toTower.toBase ≫ hΩΦ.toFanHom.algebraicMap)
    (hv : v ≫ (model τ centers(c)).2.toTower.toBase =
      (model (hΩΦ.liftRay ∘ ρ) centers(c)).2.toTower.toBase ≫ hΩΨ.toFanHom.algebraicMap)
    (f : X ≅ X') (hf : (u ≫ p) ≫ f.hom = v ≫ q) :
    f.hom.toRationalMap.comp (contractedXEvaluation b τ c hΨ q) =
      contractedXEvaluation b ρ c hΦ p := by
  have := isIntegral_internalBlowupTower b (hΩΦ.liftRay ∘ ρ) centers(c) hΩ
  have := isModification_internalBlowupTower_toBase b (hΩΦ.liftRay ∘ ρ) centers(c) hΩ
  simpa only [Scheme.RationalMap.compHom_id] using
    comp_contractedXEvaluation_of_common_model b ρ c hΦ p b τ c hΨ q u v f.hom hf (𝟙 _) (by
      have := isModification_internalBlowupTower_toBase b ρ centers(c) hΦ
      have := isModification_internalBlowupTower_toBase b τ centers(c) hΨ
      simpa only [hu, hv, Scheme.RationalMap.compHom_id] using
        (evaluation_eq_on_common_subdivision b hΩΦ hΩΨ ρ τ hρτ c
          (model (hΩΦ.liftRay ∘ ρ) centers(c)).2.toTower.toBase).symm)

private theorem pullback_eq_iff_of_common_subdivision
    {X X' : Scheme}
    (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator)
    {p : (model ρ c).1 ⟶ X} {q : (model τ c).1 ⟶ X'}
    {u : (model (hΩΦ.liftRay ∘ ρ) c).1 ⟶ (model ρ c).1}
    {v : (model (hΩΦ.liftRay ∘ ρ) c).1 ⟶ (model τ c).1}
    (hu : u ≫ (model ρ c).2.toTower.toBase =
      (model (hΩΦ.liftRay ∘ ρ) c).2.toTower.toBase ≫ hΩΦ.toFanHom.algebraicMap)
    (hv : v ≫ (model τ c).2.toTower.toBase =
      (model (hΩΦ.liftRay ∘ ρ) c).2.toTower.toBase ≫ hΩΨ.toFanHom.algebraicMap)
    {f : X ⟶ X'} (hf : (u ≫ p) ≫ f = v ≫ q)
    (hinj : Function.Injective (pullback (u ≫ p)))
    (L₀ : LineBundleClass X) (L₁ : LineBundleClass X') :
    let x := (internalBlowupPicardMarking b ρ c hΦ).symm (Additive.ofMul (pullback p L₀))
    let y := (internalBlowupPicardMarking b τ c hΨ).symm (Additive.ofMul (pullback q L₁))
    pullback f L₁ = L₀ ↔
      (Additive.ofMul (pullback hΩΦ.toFanHom.algebraicMap x.1.toMul), x.2) =
        (Additive.ofMul (pullback hΩΨ.toFanHom.algebraicMap y.1.toMul), y.2) := by
  have hmatch := hΩΦ.liftRay_comp_eq_of_primitiveGenerator_eq hΩΨ ρ τ hρτ
  have h₀ := pullback_coordinates b hΩΦ hΩ hΦ ρ rfl c u hu (pullback p L₀)
  have h₁ := pullback_coordinates b hΩΨ hΩ hΨ τ hmatch.symm c v hv (pullback q L₁)
  dsimp only
  rw [← (internalBlowupPicardMarking b (hΩΦ.liftRay ∘ ρ) c hΩ).injective.eq_iff,
    ← h₀, ← h₁, Additive.ofMul.injective.eq_iff, pullback_comp u p, pullback_comp v q, ← hf,
    ← pullback_comp (u ≫ p) f, hinj.eq_iff, eq_comm]

section SquareZero

variable {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))]
  [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of ℂ))]
  {D : X.IdealSheafData} {E : X'.IdealSheafData} {p q : ℕ}
  {P : BlowupTower X p Y} {Q : BlowupTower X' q Y'}

local notation "s" => (X ↘ Spec (CommRingCat.of ℂ))
local notation "t" => (X' ↘ Spec (CommRingCat.of ℂ))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- Two connected nef square-zero nodal pairs with matching ordered toric models
in a common oriented lattice are isomorphic as pairs over the field. The isomorphism
intertwines their fixed-center X evaluations. The marked Picard pullback is given on
the specified common subdivision by pulling back the toric classes and keeping the
total exceptional coefficients. -/
theorem exists_iso_of_matching_toric_models
    (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Multiplicative (Fin n → ℤ) →* ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P)
    (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (model ρ centers(c)).1) (a' : Y' ≅ (model τ centers(c)).1)
    (ha : a.hom ≫ (model ρ centers(c)).2.toTower.toBase ≫
      Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' : a'.hom ≫ (model τ centers(c)).2.toTower.toBase ≫
      Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : ((model ρ centers(c)).2.boundaryι.ker.comap a.hom).support = (D.comap P.toBase).support)
    (hb' : ((model τ centers(c)).2.boundaryι.ker.comap a'.hom).support = (E.comap Q.toBase).support)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hnodalD : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hnodalE : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ t))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnefD : LineBundleClass.IsNef ℂ s classOf(hD))
    (hnefE : LineBundleClass.IsNef ℂ t classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ X classOf(hD)
      classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ X' classOf(hE)
      classOf(hE) = 0) :
    letI := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
    letI := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
    let p := a.inv ≫ P.toBase
    let q := a'.inv ≫ Q.toBase
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D ∧
      f.hom.toRationalMap.comp (contractedXEvaluation b τ c hΨ q) =
        contractedXEvaluation b ρ c hΦ p ∧
      ∀ (L : LineBundleClass X) (L' : LineBundleClass X'),
        let x := (internalBlowupPicardMarking b ρ centers(c) hΦ).symm
          (Additive.ofMul (pullback p L))
        let y := (internalBlowupPicardMarking b τ centers(c) hΨ).symm
          (Additive.ofMul (pullback q L'))
        pullback f.hom L' = L ↔
          (Additive.ofMul (pullback hΩΦ.toFanHom.algebraicMap x.1.toMul), x.2) =
            (Additive.ofMul (pullback hΩΨ.toFanHom.algebraicMap y.1.toMul), y.2) := by
  have := hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  have := hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two t
  obtain ⟨m, l, W, W', T, U, e, e', hT, hU, hL, hR, hBL, hBR⟩ :=
    exists_common_nodal_refinement_internalBlowupTower b hΩΦ hΩΨ hΩ hΦ hΨ ρ τ centers(c) hρτ
  obtain ⟨V, L, f, hLT, hLf, hLD⟩ := hP.exists_append_of_iso hT a ha hb
  obtain ⟨V', R, f', hRT, hRf, hRE⟩ := hQ.exists_append_of_iso hU a' ha' hb'
  let g := f ≪≫ e.symm ≪≫ e' ≪≫ f'.symm
  have hstructure : L.toBase ≫ s = g.hom ≫ R.toBase ≫ t := by
    simp only [g, Iso.trans_hom, Iso.symm_hom, hLf, hRf, Category.assoc, ← ha, ← ha',
      Iso.inv_hom_id_assoc, reassoc_of% hR.w,
      FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
    have hleft := (reassoc_of% hL.w) Φ.algebraicRealizationStructureMap
    rw [FanHom.algebraicMap_comp_algebraicRealizationStructureMap] at hleft
    rw [← hleft, Iso.inv_hom_id_assoc]
  have hboundary : (D.comap L.toBase).radical = ((E.comap R.toBase).radical).comap g.hom := by
    simp only [g, Iso.trans_hom, Iso.symm_hom, hLD, hRE, comap_comp, ← comap_comp _ f'.inv,
      Iso.inv_hom_id, comap_id, hBR, ← hBL, ← comap_comp _ e.inv, Iso.inv_hom_id, comap_id]
  have hsupport : (D.comap L.toBase).support = ((E.comap R.toBase).comap g.hom).support := by
    simpa only [support_radical, support_comap] using congrArg
      (Scheme.IdealSheafData.support (X := V)) hboundary
  obtain ⟨iso, ⟨hiso, hfield, hpair⟩, -⟩ := hLT.existsUnique_iso_of_nef_square_zero_boundary
    ℂ hRT g hstructure hD hE hnodalD hnodalE hconn hsupport hnefD hnefE hsqD hsqE
  let u := e.hom ≫ T.toBase
  let v := e'.hom ≫ U.toBase
  dsimp only
  let p := a.inv ≫ P.toBase
  let q := a'.inv ≫ Q.toBase
  have := smoothOfRelativeDimension_internalBlowupTower b ρ centers(c) hΦ
  have := smoothOfRelativeDimension_internalBlowupTower b τ centers(c) hΨ
  have := hT.isClosedPointTower.surjective
    ((model ρ centers(c)).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
  have := hU.isClosedPointTower.surjective
    ((model τ centers(c)).2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap)
  have : IsDominant u := inferInstanceAs (IsDominant (e.hom ≫ T.toBase))
  have : IsDominant v := inferInstanceAs (IsDominant (e'.hom ≫ U.toBase))
  have hcomm : (u ≫ p) ≫ iso.hom = v ≫ q := by
    simpa only [u, v, p, q, hLf, hRf, g, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using congrArg (e.hom ≫ f.inv ≫ ·) hiso
  refine ⟨iso, hfield, hpair, comp_contractedXEvaluation_of_common_subdivision b hΩΦ hΩΨ
    hΩ hΦ hΨ ρ τ c hρτ u v hL.w hR.w iso hcomm, ?_⟩
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have hbase : u ≫ p = (e ≪≫ f.symm).hom ≫ L.toBase := by simp [u, p, hLf]
  have hinj : Function.Injective (pullback (u ≫ p)) := by
    simpa only [Function.comp_def, pullbackEquiv_apply, pullback_comp, hbase] using
      (pullbackEquiv (e ≪≫ f.symm)).injective.comp
        (hLT.isClosedPointTower.injective_pullback_toBase s)
  exact pullback_eq_iff_of_common_subdivision b hΩΦ hΩΨ hΩ hΦ hΨ ρ τ centers(c)
    hρτ hL.w hR.w hcomm hinj

end SquareZero

end TauCeti.Toric.Fan
