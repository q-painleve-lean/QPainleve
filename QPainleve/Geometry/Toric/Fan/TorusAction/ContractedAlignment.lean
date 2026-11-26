/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Contraction
public import QPainleve.Geometry.Toric.Fan.TorusAction.Contraction

import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Translation between contracted toric presentations

A torus translation aligning the ordered internal centers descends to the original
surfaces when the nodal contraction is determined by a connected nef boundary of
square zero. The descended isomorphism preserves the Picard coordinates obtained by
pullback to the ordered models.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) {c d : Fin n → ℂˣ}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "M" a:arg => internalBlowupTower b s a
local notation "Y" a:arg => Sigma.fst (M a)
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (M a))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (M a))
local notation "base" => Φ.algebraicRealizationStructureMap
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

/-- A translating lift between two ordered models descends uniquely through their nodal
contractions when both original boundaries are nef and square zero and the source
boundary is connected. The descent identifies the boundary ideals and preserves the
Picard coordinates. -/
theorem existsUnique_iso_of_translation_of_nef_square_zero_boundary
    (hΦ : Φ.IsRegular) {X X' Z Z' : Scheme} [IsIntegral X] [IsIntegral X']
    [X.Over S] [X'.Over S] [X.IsProjectiveOver ℂ] [X'.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (X' ↘ S)]
    {D : X.IdealSheafData} {D' : X'.IdealSheafData}
    {r r' : ℕ} {P : BlowupTower X r Z} {Q : BlowupTower X' r' Z'}
    (hP : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) P)
    (hQ : IsNodalBoundaryTower D' (X' ↘ S) (𝟙 X') Q)
    (e : Z ≅ Y c) (e' : Z' ≅ Y d)
    (he : e.inv ≫ P.toBase ≫ (X ↘ S) = (T c).toBase ≫ base)
    (he' : e'.inv ≫ Q.toBase ≫ (X' ↘ S) = (T d).toBase ≫ base)
    (hD : ((D.comap P.toBase).comap e.inv).support = (ι c).ker.support)
    (hD' : ((D'.comap Q.toBase).comap e'.inv).support = (ι d).ker.support)
    {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {g : Y c ≅ Y d}
    (hg : IsLift (Φ.torusTranslation χ) (T c) (T d) g)
    (hC : D.IsEffectiveCartier) (hC' : D'.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ (X ↘ S)))
    (hnodal' : AtWorstNodalOfRelativeDimensionOne (D'.subschemeι ≫ (X' ↘ S)))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnef : IsNef ℂ (X ↘ S) classOf(hC)) (hnef' : IsNef ℂ (X' ↘ S) classOf(hC'))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hC) classOf(hC) = 0)
    (hsq' : Chow.classIntersectionNumber ℂ X' classOf(hC') classOf(hC') = 0) :
    ∃! f : X ≅ X', P.toBase ≫ f.hom = e.hom ≫ g.hom ≫ e'.inv ≫ Q.toBase ∧
      f.hom ≫ (X' ↘ S) = (X ↘ S) ∧ D'.comap f.hom = D ∧
      ∀ L : LineBundleClass X',
        (internalBlowupPicardMarking b s c hΦ).symm
          (Additive.ofMul (pullback (e.inv ≫ P.toBase) (pullback f.hom L))) =
        (internalBlowupPicardMarking b s d hΦ).symm
          (Additive.ofMul (pullback (e'.inv ≫ Q.toBase) L)) := by
  let a := e ≪≫ g ≪≫ e'.symm
  have hbase := hom_comp_internalBlowupTower_structureMap_of_isLift_torusTranslation
    b s c d χ hg
  have hover : P.toBase ≫ (X ↘ S) = a.hom ≫ Q.toBase ≫ (X' ↘ S) := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc, he', hbase, ← he,
      Iso.hom_inv_id_assoc]
  have hsupp := support_comap_contraction_of_translation b s c d hg
    (by simpa only [Scheme.IdealSheafData.comap_comp] using hD)
    (by simpa only [Scheme.IdealSheafData.comap_comp] using hD')
  have hsupp' : (D.comap P.toBase).support = ((D'.comap Q.toBase).comap a.hom).support := by
    have h := congrArg (fun F ↦ F.preimage e.hom.continuous) hsupp
    simpa only [a, Iso.trans_hom, Iso.symm_hom, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.support_comap, Category.assoc, Iso.hom_inv_id_assoc] using h
  obtain ⟨f, ⟨hf, hfOver, hfD⟩, huniq⟩ :=
    hP.existsUnique_iso_of_nef_square_zero_boundary ℂ hQ a hover hC hC'
      hnodal hnodal' hconn hsupp' hnef hnef' hsq hsq'
  have hf' : P.toBase ≫ f.hom = e.hom ≫ g.hom ≫ e'.inv ≫ Q.toBase := by
    simpa only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hf
  refine ⟨f, ⟨hf', hfOver, hfD, fun L ↦ ?_⟩, fun j hj ↦ huniq j ⟨?_, hj.2.1, hj.2.2.1⟩⟩
  · have hcomm : (e.inv ≫ P.toBase) ≫ f.hom = g.hom ≫ e'.inv ≫ Q.toBase := by
      rw [Category.assoc, hf', Iso.inv_hom_id_assoc]
    let t : ContractedToricTranslation b s (e.inv ≫ P.toBase) (e'.inv ≫ Q.toBase) f :=
      ⟨χ, g, hg, hcomm⟩
    exact t.pullback_marking hΦ L
  · simpa only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hj.1

end TauCeti.Toric.Fan
