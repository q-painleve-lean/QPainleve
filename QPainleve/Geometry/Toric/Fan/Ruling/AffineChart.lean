/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Basic

import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# Affine toric charts of the projective line

The positive and negative rays each define an affine open subfan. Their scheme
realizations embed as open subschemes and cover the projective line.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "P₁" => Fan.projectiveSpace (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)

/-- The positive ray for chart zero and the negative ray for chart one. -/
abbrev projectiveLineAffineRay (k : Fin 2) : PointedCone ℝ (Fin 1 → ℝ) :=
  if k = 0 then affineRayCone else negativeRayCone

/-- The ray defining either affine chart is a cone of the projective-line fan. -/
theorem projectiveLineAffineRay_mem (k : Fin 2) : projectiveLineAffineRay k ∈ (P₁).cones := by
  rw [projectiveSpace_finOne_eq_projectiveLineFan]
  fin_cases k
  · exact affineRayCone_mem_projectiveLineFan
  · exact negativeRayCone_mem_projectiveLineFan

/-- The subfan of the projective line on the positive ray for index zero and on
the negative ray for index one. -/
@[expose, implicit_reducible]
def projectiveLineAffineFan (k : Fin 2) :=
  (P₁).subfan {τ | τ.IsFaceOf (projectiveLineAffineRay k)}
    ((P₁).isFaceOf_subset_cones (projectiveLineAffineRay_mem k)) fun _ _ hσ hτ ↦ hτ.trans hσ

/-- The cones of the affine chart are the faces of its chosen ray. -/
theorem mem_projectiveLineAffineFan_cones {k : Fin 2} {σ : PointedCone ℝ (Fin 1 → ℝ)} :
    σ ∈ (projectiveLineAffineFan k).cones ↔
      σ.IsFaceOf (if k = 0 then affineRayCone else negativeRayCone) := by
  rw [projectiveLineAffineFan, Fan.subfan_cones]
  rfl

/-- Each affine chart is a subfan of the projective-line fan. -/
theorem projectiveLineAffineFan_cones_subset (k : Fin 2) :
    (projectiveLineAffineFan k).cones ⊆ (P₁).cones :=
  (P₁).isFaceOf_subset_cones (projectiveLineAffineRay_mem k)

/-- The fan map including the affine chart into the projective-line fan. -/
abbrev projectiveLineAffineFanInclusion (k : Fin 2) : FanHom (projectiveLineAffineFan k) P₁ :=
  (P₁).subfanInclusion (projectiveLineAffineFan k).cones (projectiveLineAffineFan_cones_subset k)
    (projectiveLineAffineFan k).mem_of_isFaceOf

/-- The inclusion of the affine toric chart into the projective line. -/
def projectiveLineAffineFanι (k : Fin 2) :
    (projectiveLineAffineFan k).algebraicRealization ⟶ projectiveLine ℂ :=
  (projectiveLineAffineFanInclusion k).algebraicMap ≫ projectiveLineToricIso.hom

/-- The chart immersion is induced by the fan inclusion and the toric comparison. -/
theorem projectiveLineAffineFanι_def (k : Fin 2) :
    projectiveLineAffineFanι k =
      (projectiveLineAffineFanInclusion k).algebraicMap ≫ projectiveLineToricIso.hom :=
  (rfl)

instance (k : Fin 2) : IsOpenImmersion (projectiveLineAffineFanι k) := by
  rw [projectiveLineAffineFanι]
  let : IsOpenImmersion (projectiveLineAffineFanInclusion k).algebraicMap :=
    (P₁).isOpenImmersion_subfanInclusion_algebraicMap
      (projectiveLineAffineFan k).cones (projectiveLineAffineFan_cones_subset k)
      (projectiveLineAffineFan k).mem_of_isFaceOf
  infer_instance

instance (k : Fin 2) : IsAffine (projectiveLineAffineFan k).algebraicRealization := by
  let U := projectiveLineAffineFan k
  let σ : U.cones := ⟨projectiveLineAffineRay k, mem_projectiveLineAffineFan_cones.mpr (.refl _)⟩
  have : IsIso (U.affineToricChartι σ) :=
    U.isIso_affineToricChartι_of_forall_le (σ := σ) fun τ ↦
      (mem_projectiveLineAffineFan_cones.mp τ.property).le
  exact IsAffine.of_isIso (inv (U.affineToricChartι σ))

/-- The toric affine chart corresponds to the polynomial chart at the same coordinate. -/
def projectiveLineAffineFanIso (k : Fin 2) :
    (projectiveLineAffineFan k).algebraicRealization ≅ Spec (.of (Polynomial ℂ)) := by
  let U := projectiveLineAffineFan k
  let σ : U.cones := ⟨projectiveLineAffineRay k, mem_projectiveLineAffineFan_cones.mpr (.refl _)⟩
  let j := U.affineToricChartι σ
  let : IsIso j :=
    U.isIso_affineToricChartι_of_forall_le fun τ ↦
      (mem_projectiveLineAffineFan_cones.mp τ.property).le
  let f := j ≫ projectiveLineAffineFanι k
  let τ := projectiveSpaceMaximalCone (Pi.basisFun ℤ (Fin 1)) (isIntegralLattice_intCast 1)
    (finSuccEquiv 1 k)
  let σ' : (P₁).cones := ⟨σ.val, projectiveLineAffineFan_cones_subset k σ.property⟩
  have hτ : σ' = τ :=
    Subtype.ext (projectiveSpaceMaximalCone_finOne_val k).symm
  have hj : j ≫ (projectiveLineAffineFanInclusion k).algebraicMap = (P₁).affineToricChartι σ' :=
    affineToricChartι_comp_subfanInclusion_algebraicMap P₁ U.cones
      (projectiveLineAffineFan_cones_subset k) U.mem_of_isFaceOf σ
  have hf : Set.range f = Set.range (projectiveLine.polynomialChartι ℂ k) := by
    dsimp only [f]
    rw [projectiveLineAffineFanι_def, ← Category.assoc, hj]
    exact (congrArg (fun σ : (P₁).cones ↦
      Set.range ((P₁).affineToricChartι σ ≫ projectiveLineToricIso.hom)) hτ).trans
      (range_affineToricChartι_comp_projectiveLineToricIso k)
  exact (asIso j).symm ≪≫ IsOpenImmersion.isoOfRangeEq f (projectiveLine.polynomialChartι ℂ k) hf

/-- The polynomial chart comparison commutes with the two open immersions. -/
@[reassoc]
theorem projectiveLineAffineFanIso_hom_comp_polynomialChartι (k : Fin 2) :
    (projectiveLineAffineFanIso k).hom ≫ projectiveLine.polynomialChartι ℂ k =
      projectiveLineAffineFanι k := by
  simp [projectiveLineAffineFanIso, IsOpenImmersion.isoOfRangeEq_hom_fac]

/-- The affine toric chart and the corresponding polynomial chart have the same image. -/
theorem range_projectiveLineAffineFanι (k : Fin 2) :
    Set.range (projectiveLineAffineFanι k) = Set.range (projectiveLine.polynomialChartι ℂ k) := by
  rw [← projectiveLineAffineFanIso_hom_comp_polynomialChartι]
  exact (Scheme.homeoOfIso (projectiveLineAffineFanIso k)).surjective.range_comp _

/-- Each point of the projective line belongs to one of the two affine toric charts. -/
theorem exists_projectiveLineAffineFanι_apply_eq (x : projectiveLine ℂ) :
    ∃ (k : Fin 2) (y : (projectiveLineAffineFan k).algebraicRealization),
      projectiveLineAffineFanι k y = x := by
  obtain ⟨σ, y, hy⟩ :=
    (P₁).exists_affineToricChartι_apply_eq (projectiveLineToricIso.inv x)
  have hσ : ∃ k : Fin 2, σ.val ∈ (projectiveLineAffineFan k).cones := by
    have hs := σ.property
    simp only [projectiveSpace_finOne_eq_projectiveLineFan,
      mem_projectiveLineFan_cones] at hs
    rcases hs with h | h | h
    · exact ⟨0, mem_projectiveLineAffineFan_cones.mpr
        (h ▸ isRegularCone_affineRayCone.toIsToricCone.salient.bot_isFaceOf)⟩
    · exact ⟨0, mem_projectiveLineAffineFan_cones.mpr (h ▸ .refl _)⟩
    · exact ⟨1, mem_projectiveLineAffineFan_cones.mpr (h ▸ .refl _)⟩
  obtain ⟨k, hk⟩ := hσ
  let τ : (projectiveLineAffineFan k).cones := ⟨σ.val, hk⟩
  have hτ : (projectiveLineAffineFan k).affineToricChartι τ ≫
      (projectiveLineAffineFanInclusion k).algebraicMap = (P₁).affineToricChartι σ :=
    affineToricChartι_comp_subfanInclusion_algebraicMap P₁
      (projectiveLineAffineFan k).cones (projectiveLineAffineFan_cones_subset k)
      (projectiveLineAffineFan k).mem_of_isFaceOf τ
  refine ⟨k, (projectiveLineAffineFan k).affineToricChartι τ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, projectiveLineAffineFanι, ← Category.assoc, hτ,
    Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

end TauCeti.Toric.Fan
