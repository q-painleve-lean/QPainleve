/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction
public import QPainleve.Geometry.Toric.Fan.Boundary.NodalPullback
public import QPainleve.Geometry.Toric.Fan.Subdivision.InternalBlowup

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.Geometry.Toric.Fan.CommonRefinement
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Common nodal refinements of internal toric blowup models

Two regular surface fans with the same support and matching ordered binomial centers
can be compared on a common internal model. Both projections are nodal blowup towers
up to isomorphism, and their reduced total boundaries are identified with the strict
boundary of the internal model over the subdividing fan.

For toric models with infinitely near centers and blowups of boundary nodes, see
[Gross, Hacking and Keel, Definition 1.2 and the paragraph following it][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  (b : Module.Basis (Fin 2) ℤ N) {n : ℕ}

local notation "model" => internalBlowupTower b

/-- A regular subdivision induces a nodal blowup projection of the ordered internal
model. Its reduced total boundary is the strict boundary of the refined internal model,
and the square of projections to the fan schemes is cartesian. -/
theorem IsSubdivision.exists_nodal_refinement_internalBlowupTower
    (h : Φ.IsSubdivision Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (ρ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ) :
    let A := model (h.liftRay ∘ ρ) c
    let B := model ρ c
    ∃ (m : ℕ) (Z : Scheme) (T : BlowupTower B.1 m Z) (e : A.1 ≅ Z),
      IsNodalBoundaryTower B.2.boundaryι.ker
        (B.2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap) (𝟙 B.1) T ∧
      IsPullback (e.hom ≫ T.toBase) A.2.toTower.toBase
        B.2.toTower.toBase h.toFanHom.algebraicMap ∧
      ((B.2.boundaryι.ker.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker := by
  dsimp only
  let A := model (h.liftRay ∘ ρ) c
  let B := model ρ c
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨m, Y, R, a, hR, ha, -, -⟩ :=
    h.exists_toric_subdivision_blowup_tower hΨ hΦ hΨ₀ hrank
  obtain ⟨Z, T, g, hT, hg⟩ :=
    Ψ.exists_isPullback_nodalBoundaryTower_internalBlowupTower hR b ρ c
  obtain ⟨g', hg', hb, -⟩ := h.exists_isPullback_internalBlowupTower b ρ c
  have hpb : IsPullback T.toBase (g ≫ a.inv) B.2.toTower.toBase
      h.toFanHom.algebraicMap := by
    refine hg.flip.of_iso' (Iso.refl _) (Iso.refl _) a (Iso.refl _)
      (by simp) (by simp) (by simp [B]) (by simpa using ha)
  let e := hg'.isoIsPullback _ _ hpb
  have he : e.hom ≫ T.toBase = g' := hg'.isoIsPullback_hom_fst _ _ hpb
  refine ⟨m, Z, T, e, hT, he.symm ▸ hg', ?_⟩
  have hred : IsReduced (Φ.boundaryIdeal hΦ₀).subscheme := by
    rw [Fan.boundaryIdeal_def]
    infer_instance
  have hbase :
      (((B.2.boundaryι ≫ B.2.toTower.toBase).ker).comap h.toFanHom.algebraicMap).radical =
        (A.2.boundaryι ≫ A.2.toTower.toBase).ker := by
    simpa only [WithBoundary.boundaryι_toBase, ker_subschemeι] using
      h.radical_comap_boundaryIdeal hΦ₀ hΨ₀
  have : IsClosedImmersion (B.2.boundaryι ≫ B.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have : IsClosedImmersion (A.2.boundaryι ≫ A.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have hcart : IsPullback g' A.2.toTower.toBase B.2.toTower.toBase
      h.toFanHom.algebraicMap := hg'
  have hboundary := radical_comap_ker_eq_of_isPullback hcart B.2.boundaryι A.2.boundaryι
    (h.boundaryMap hΦ₀ hΨ₀) hb hbase
  rw [← radical_comap_of_isOpenImmersion, ← comap_comp, he]
  exact hboundary

/-- Ordered internal models on regular surface fans with the same support have a
common nodal refinement when the labeled primitive generators and parameters agree.
The refined model has nodal projections to both internal models and is the cartesian
pullback of each along the corresponding fan subdivision. Both reduced total
boundaries are its strict boundary. -/
theorem exists_common_nodal_refinement_internalBlowupTower
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hs : Φ.support = Ψ.support)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator) :
    let B := model ρ c
    let C := model τ c
    ∃ (Ω : Fan i) (hΩΦ : Ω.IsSubdivision Φ) (hΩΨ : Ω.IsSubdivision Ψ)
      (_ : Ω.IsRegular) (hΩ₀ : Nonempty Ω.cones),
      let A := internalBlowupTower (h₀ := hΩ₀) b (hΩΦ.liftRay ∘ ρ) c
      ∃ (m l : ℕ) (Y Z : Scheme) (T : BlowupTower B.1 m Y) (U : BlowupTower C.1 l Z)
        (e : A.1 ≅ Y) (f : A.1 ≅ Z),
        IsNodalBoundaryTower B.2.boundaryι.ker
          (B.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap) (𝟙 B.1) T ∧
        IsNodalBoundaryTower C.2.boundaryι.ker
          (C.2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap) (𝟙 C.1) U ∧
        IsPullback (e.hom ≫ T.toBase) A.2.toTower.toBase
          B.2.toTower.toBase hΩΦ.toFanHom.algebraicMap ∧
        IsPullback (f.hom ≫ U.toBase) A.2.toTower.toBase
          C.2.toTower.toBase hΩΨ.toFanHom.algebraicMap ∧
        ((B.2.boundaryι.ker.comap T.toBase).radical).comap e.hom = A.2.boundaryι.ker ∧
        ((C.2.boundaryι.ker.comap U.toBase).radical).comap f.hom = A.2.boundaryι.ker := by
  dsimp only
  have hrank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, hΩΦ, hΩΨ, hΩ⟩ := Φ.exists_regular_common_subdivision Ψ hΦ hΨ hrank hs
  let hΩ₀ := hΩΦ.nonempty_cones_of_nonempty hΦ₀
  have hmatch : hΩΦ.liftRay ∘ ρ = hΩΨ.liftRay ∘ τ := by
    funext j
    apply Ray.primitiveGenerator_injective
    simpa only [Function.comp_apply, IsSubdivision.primitiveGenerator_liftRay] using hρτ j
  obtain ⟨m, Y, T, e, hT, he, hD⟩ :=
    hΩΦ.exists_nodal_refinement_internalBlowupTower b hΩ hΦ ρ c
  have hright := hΩΨ.exists_nodal_refinement_internalBlowupTower b hΩ hΨ τ c
  dsimp only at hright
  rw [← hmatch] at hright
  obtain ⟨l, Z, U, f, hU, hf, hE⟩ := hright
  exact ⟨Ω, hΩΦ, hΩΨ, hΩ, hΩ₀, m, l, Y, Z, T, U, e, f, hT, hU, he, hf, hD, hE⟩

section SquareZero

open TauCeti.AlgebraicGeometry

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
in a common oriented lattice are isomorphic as pairs over the field. The endpoint
toric models may use different regular fans of the same support. -/
theorem exists_iso_of_matching_toric_models
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hs : Φ.support = Ψ.support)
    (ρ : Fin n → Φ.Ray) (τ : Fin n → Ψ.Ray) (c : Fin n → ℂˣ)
    (hρτ : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator)
    (hP : IsNodalBoundaryTower D s (𝟙 X) P)
    (hQ : IsNodalBoundaryTower E t (𝟙 X') Q)
    (a : Y ≅ (model ρ c).1) (a' : Y' ≅ (model τ c).1)
    (ha : a.hom ≫ (model ρ c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap = P.toBase ≫ s)
    (ha' :
      a'.hom ≫ (model τ c).2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap = Q.toBase ≫ t)
    (hb : ((model ρ c).2.boundaryι.ker.comap a.hom).support = (D.comap P.toBase).support)
    (hb' : ((model τ c).2.boundaryι.ker.comap a'.hom).support = (E.comap Q.toBase).support)
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
    ∃ f : X ≅ X', f.hom ≫ t = s ∧ E.comap f.hom = D := by
  obtain ⟨Ω, hΩΦ, hΩΨ, -, hΩ₀, m, l, W, W', T, U, e, e', hT, hU, hL, hR, hBL, hBR⟩ :=
    exists_common_nodal_refinement_internalBlowupTower b hΦ hΨ hs ρ τ c hρτ
  obtain ⟨V, L, f, hLT, hLf, hLD⟩ := hP.exists_append_of_iso hT a ha hb
  obtain ⟨V', R, f', hRT, hRf, hRE⟩ := hQ.exists_append_of_iso hU a' ha' hb'
  let g := f ≪≫ e.symm ≪≫ e' ≪≫ f'.symm
  have haux :
      e.hom ≫ T.toBase ≫ (model ρ c).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap =
        e'.hom ≫ U.toBase ≫ (model τ c).2.toTower.toBase ≫ Ψ.algebraicRealizationStructureMap := by
    have hleft := (reassoc_of% hL.w) Φ.algebraicRealizationStructureMap
    have hright := (reassoc_of% hR.w) Ψ.algebraicRealizationStructureMap
    simp only [FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
      at hleft hright
    exact hleft.trans hright.symm
  have hstructure : L.toBase ≫ s = g.hom ≫ R.toBase ≫ t := by
    simp only [g, Iso.trans_hom, Iso.symm_hom, hLf, hRf, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← ha, ← ha', Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    simp only [← haux, Iso.inv_hom_id_assoc]
  have hboundary : (D.comap L.toBase).radical = ((E.comap R.toBase).radical).comap g.hom := by
    simp only [g, Iso.trans_hom, Iso.symm_hom, hLD, hRE, comap_comp, ← comap_comp _ f'.inv,
      Iso.inv_hom_id, comap_id, hBR, ← hBL, ← comap_comp _ e.inv, Iso.inv_hom_id, comap_id]
  have hsupport : (D.comap L.toBase).support = ((E.comap R.toBase).comap g.hom).support := by
    simpa only [support_radical, support_comap] using congrArg
      (Scheme.IdealSheafData.support (X := V)) hboundary
  obtain ⟨iso, ⟨-, hfield, hpair⟩, -⟩ := hLT.existsUnique_iso_of_nef_square_zero_boundary
    ℂ hRT g hstructure hD hE hnodalD hnodalE hconn hsupport hnefD hnefE hsqD hsqE
  exact ⟨iso, hfield, hpair⟩

end SquareZero

end TauCeti.Toric.Fan
