/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Laurent

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.BaseChange
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic

/-!
# Polynomial coordinates on toric ruling products

The products over the two affine charts of the base projective line are projective
lines over polynomial rings. Their restrictions to the base torus are the native
coefficient-change projections, with the affine coordinate sent to the Laurent
parameter on the first chart and to its reciprocal on the second.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits LaurentPolynomial
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "A" => Polynomial ℂ
local notation "L" => LaurentPolynomial ℂ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => projectiveLine ℂ
local notation "p" => (P ↘ S)
local notation "t" => (projectiveLineTorusFan.algebraicRealization ↘ S)
local notation "s[" k "]" => Fan.algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "a[" k "]" => FanHom.algebraicMap (projectiveLineTorusToAffineFan k)
local notation "U[" k "]" => projectiveLineAffineFanIso k

/-- Restriction of a polynomial in the indicated base chart to the torus with
Laurent coordinate `X₁ / X₀`. -/
def projectiveLineTorusToAffinePolynomial (k : Fin 2) : A →+* L :=
  Polynomial.eval₂RingHom (algebraMap ℂ L) (T (if k = 0 then 1 else -1))

/-- Restriction sends constant polynomials to the same Laurent constants. -/
@[simp]
theorem projectiveLineTorusToAffinePolynomial_C (k : Fin 2) (c : ℂ) :
    projectiveLineTorusToAffinePolynomial k (Polynomial.C c) = algebraMap ℂ L c := by
  simp [projectiveLineTorusToAffinePolynomial]

/-- The two affine coordinates restrict to the Laurent parameter and its reciprocal. -/
@[simp]
theorem projectiveLineTorusToAffinePolynomial_X (k : Fin 2) :
    projectiveLineTorusToAffinePolynomial k Polynomial.X = T (if k = 0 then 1 else -1) := by
  simp [projectiveLineTorusToAffinePolynomial]

local notation "l[" k "]" => Spec.map (CommRingCat.ofHom (projectiveLineTorusToAffinePolynomial k))

/-- The toric inclusion into either chart is restriction to the corresponding
Laurent coordinate, expressed through the affine base chart comparisons. -/
@[reassoc]
theorem projectiveLineTorusToAffine_algebraicMap_comp_affineFanIso (k : Fin 2) :
    a[k] ≫ (U[k]).hom = projectiveLineTorusIsoSpecLaurent.hom ≫ l[k] := by
  apply (cancel_mono (projectiveLine.polynomialChartι ℂ k)).mp
  rw [Category.assoc, projectiveLineAffineFanIso_hom_comp_polynomialChartι,
    projectiveLineTorusToAffineFan_algebraicMap_comp_ι, Category.assoc]
  have hzero : projectiveLine.polynomialPoint ℂ (algebraMap ℂ L) 0 (T 1) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ projectiveLine.polynomialChartι ℂ 0 := by
    rw [projectiveLine.polynomialPoint_def]
    congr 2
    ext <;> simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  have hchart : l[k] ≫ projectiveLine.polynomialChartι ℂ k =
      projectiveLine.polynomialPoint ℂ (algebraMap ℂ L) 0 (T 1) := by
    rw [projectiveLineTorusToAffinePolynomial, ← projectiveLine.polynomialPoint_def]
    fin_cases k
    · simp
    · simpa [genericUnit_val, genericUnit_inv] using
        (projectiveLine.polynomialPoint_rev (algebraMap ℂ L) (0 : Fin 2) (genericUnit ℂ)).symm
  rw [hchart, hzero, projectiveLineTorusIsoSpecLaurent_hom_comp_chart]

/-- The polynomial chart comparison respects the structure morphism over `ℂ`. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineFanIso_hom_comp_toBase (k : Fin 2) :
    (U[k]).hom ≫ Spec.algebraMap ℂ A = s[k] := by
  rw [Spec.algebraMap, ← projectiveLine.polynomialChartι_over ℂ k,
    projectiveLineAffineFanIso_hom_comp_polynomialChartι_assoc,
    projectiveLineAffineFanι_def, Category.assoc, CategoryTheory.comp_over,
    Fan.algebraicRealization_over, FanHom.algebraicMap_comp_algebraicRealizationStructureMap]

private theorem isPullback_projectiveLinePolynomialProduct (k : Fin 2) :
    IsPullback (projectiveLine.baseChangeProjection ℂ A)
      ((projectiveLine A ↘ Spec (.of A)) ≫ (U[k]).inv) p s[k] := by
  refine (projectiveLine.isPullback_baseChangeProjection ℂ A).of_iso'
    (Iso.refl _) (Iso.refl _) (U[k]) (Iso.refl _) (by simp) (by simp) (by simp) ?_
  simpa only [Iso.refl_hom, Category.comp_id] using projectiveLineAffineFanIso_hom_comp_toBase k

/-- The product with the affine toric base chart, in polynomial coordinates on the base. -/
def projectiveLineAffineProductIsoPolynomial (k : Fin 2) :
    pullback p s[k] ≅ projectiveLine A :=
  (isPullback_projectiveLinePolynomialProduct k).isoPullback.symm

/-- The polynomial comparison preserves the projective-line projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineProductIsoPolynomial_hom_baseChangeProjection (k : Fin 2) :
    (projectiveLineAffineProductIsoPolynomial k).hom ≫ projectiveLine.baseChangeProjection ℂ A =
      pullback.fst p s[k] :=
  (isPullback_projectiveLinePolynomialProduct k).isoPullback_inv_fst

/-- The structural map of the polynomial model reads the affine base projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineProductIsoPolynomial_hom_toBase (k : Fin 2) :
    (projectiveLineAffineProductIsoPolynomial k).hom ≫ (projectiveLine A ↘ Spec (.of A)) =
      pullback.snd p s[k] ≫ (U[k]).hom := by
  apply (cancel_mono (U[k]).inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (isPullback_projectiveLinePolynomialProduct k).isoPullback_inv_snd

/-- The product with the base torus, in Laurent coordinates on the base. -/
def projectiveLineTorusPullbackIsoLaurent :
    pullback p t ≅ projectiveLine L :=
  isPullback_projectiveLineTorusProduct.isoPullback.symm ≪≫ projectiveLineTorusProductIsoLaurent

/-- In the product fan realization the Laurent comparison is the existing product fan
isomorphism. -/
theorem projectiveLineTorusPullbackIsoLaurent_def :
    projectiveLineTorusPullbackIsoLaurent =
      isPullback_projectiveLineTorusProduct.isoPullback.symm ≪≫
        projectiveLineTorusProductIsoLaurent :=
  (rfl)

/-- The Laurent comparison preserves the projective-line projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPullbackIsoLaurent_hom_baseChangeProjection :
    projectiveLineTorusPullbackIsoLaurent.hom ≫ projectiveLine.baseChangeProjection ℂ L =
      pullback.fst p t := by
  simp [projectiveLineTorusPullbackIsoLaurent]

/-- The structural map of the Laurent model reads the Laurent base projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPullbackIsoLaurent_hom_toBase :
    projectiveLineTorusPullbackIsoLaurent.hom ≫ (projectiveLine L ↘ Spec (.of L)) =
      pullback.snd p t ≫ projectiveLineTorusIsoSpecLaurent.hom := by
  simp [projectiveLineTorusPullbackIsoLaurent]

/-- On both affine product charts, the inclusion of the Laurent overlap is
projective-line base change along restriction of the base coordinate. -/
@[reassoc]
theorem projectiveLineTorusProductToAffine_comp_polynomialIso (k : Fin 2) :
    projectiveLineTorusProductToAffine k ≫ (projectiveLineAffineProductIsoPolynomial k).hom =
      projectiveLineTorusPullbackIsoLaurent.hom ≫
        @projectiveLine.baseChangeProjection A _ L _
          (projectiveLineTorusToAffinePolynomial k).toAlgebra := by
  let : Algebra A L := (projectiveLineTorusToAffinePolynomial k).toAlgebra
  have hcoeff : algebraMap A L = projectiveLineTorusToAffinePolynomial k :=
    RingHom.algebraMap_toAlgebra _
  let : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [hcoeff]
    simp
  apply (projectiveLine.isPullback_baseChangeProjection ℂ A).hom_ext
  · simp
  · rw [Category.assoc, projectiveLineAffineProductIsoPolynomial_hom_toBase,
      projectiveLineTorusProductToAffine_snd_assoc, Category.assoc,
      projectiveLineTorusToAffine_algebraicMap_comp_affineFanIso,
      (projectiveLine.isPullback_baseChangeProjection A L).w,
      projectiveLineTorusPullbackIsoLaurent_hom_toBase_assoc, hcoeff]

end TauCeti.Toric.Fan
