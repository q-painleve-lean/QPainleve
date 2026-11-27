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

variable (K : Type) [CommRing K]

local notation "A" => Polynomial K
local notation "L" => LaurentPolynomial K
local notation "S" => Spec (CommRingCat.of K)
local notation "P" => projectiveLine K
local notation "p" => (P ↘ S)
local notation "t" => ((projectiveLineTorusFan.finiteFanScheme K) ↘ S)
local notation "s[" k "]" => Fan.finiteFanSchemeToSpec K (projectiveLineAffineFan k)
local notation "a[" k "]" => FanHom.finiteFanSchemeHom K (projectiveLineTorusToAffineFan k)
local notation "U[" k "]" => projectiveLineAffineFanIso K k

/-- Restriction of a polynomial in the indicated base chart to the torus with
Laurent coordinate `X₁ / X₀`. -/
def projectiveLineTorusToAffinePolynomial (k : Fin 2) : A →+* L :=
  Polynomial.eval₂RingHom (algebraMap K L) (T (if k = 0 then 1 else -1))

/-- Restriction sends constant polynomials to the same Laurent constants. -/
@[simp]
theorem projectiveLineTorusToAffinePolynomial_C (k : Fin 2) (c : K) :
    projectiveLineTorusToAffinePolynomial K k (Polynomial.C c) = algebraMap K L c := by
  simp [projectiveLineTorusToAffinePolynomial]

/-- The two affine coordinates restrict to the Laurent parameter and its reciprocal. -/
@[simp]
theorem projectiveLineTorusToAffinePolynomial_X (k : Fin 2) :
    projectiveLineTorusToAffinePolynomial K k Polynomial.X = T (if k = 0 then 1 else -1) := by
  simp [projectiveLineTorusToAffinePolynomial]

local notation "l[" k "]" =>
  Spec.map (CommRingCat.ofHom (projectiveLineTorusToAffinePolynomial K k))

/-- The toric inclusion into either chart is restriction to the corresponding
Laurent coordinate, expressed through the affine base chart comparisons. -/
@[reassoc]
theorem projectiveLineTorusToAffine_algebraicMap_comp_affineFanIso (k : Fin 2) :
    a[k] ≫ (U[k]).hom = (projectiveLineTorusIsoSpecLaurent K).hom ≫ l[k] := by
  apply (cancel_mono (projectiveLine.polynomialChartι K k)).mp
  rw [Category.assoc, projectiveLineAffineFanIso_hom_comp_polynomialChartι,
    projectiveLineTorusToAffineFan_algebraicMap_comp_ι, Category.assoc]
  have hzero : projectiveLine.polynomialPoint K (algebraMap K L) 0 (T 1) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ projectiveLine.polynomialChartι K 0 := by
    rw [projectiveLine.polynomialPoint_def]
    congr 2
    ext <;> simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  have hchart : l[k] ≫ projectiveLine.polynomialChartι K k =
      projectiveLine.polynomialPoint K (algebraMap K L) 0 (T 1) := by
    rw [projectiveLineTorusToAffinePolynomial, ← projectiveLine.polynomialPoint_def]
    fin_cases k
    · simp
    · simpa [genericUnit_val, genericUnit_inv] using
        (projectiveLine.polynomialPoint_rev (algebraMap K L) (0 : Fin 2) (genericUnit K)).symm
  rw [hchart, hzero, projectiveLineTorusIsoSpecLaurent_hom_comp_chart]

private theorem isPullback_projectiveLinePolynomialProduct (k : Fin 2) :
    IsPullback (projectiveLine.baseChangeProjection K A)
      ((projectiveLine A ↘ Spec (.of A)) ≫ (U[k]).inv) p s[k] := by
  refine (projectiveLine.isPullback_baseChangeProjection K A).of_iso'
    (Iso.refl _) (Iso.refl _) (U[k]) (Iso.refl _) (by simp) (by simp) (by simp) ?_
  simpa only [Iso.refl_hom, Category.comp_id] using projectiveLineAffineFanIso_hom_comp_toBase K k

/-- The product with the affine toric base chart, in polynomial coordinates on the base. -/
def projectiveLineAffineProductIsoPolynomial (k : Fin 2) :
    pullback p s[k] ≅ projectiveLine A :=
  (isPullback_projectiveLinePolynomialProduct K k).isoPullback.symm

/-- The polynomial comparison preserves the projective-line projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineProductIsoPolynomial_hom_baseChangeProjection (k : Fin 2) :
    (projectiveLineAffineProductIsoPolynomial K k).hom ≫ projectiveLine.baseChangeProjection K A =
      pullback.fst p s[k] :=
  (isPullback_projectiveLinePolynomialProduct K k).isoPullback_inv_fst

/-- The structural map of the polynomial model reads the affine base projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineProductIsoPolynomial_hom_toBase (k : Fin 2) :
    (projectiveLineAffineProductIsoPolynomial K k).hom ≫ (projectiveLine A ↘ Spec (.of A)) =
      pullback.snd p s[k] ≫ (U[k]).hom := by
  apply (cancel_mono (U[k]).inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (isPullback_projectiveLinePolynomialProduct K k).isoPullback_inv_snd

/-- The product with the base torus, in Laurent coordinates on the base. -/
def projectiveLineTorusPullbackIsoLaurent :
    pullback p t ≅ projectiveLine L :=
  (isPullback_projectiveLineTorusProduct K).isoPullback.symm ≪≫
    projectiveLineTorusProductIsoLaurent K

/-- In the product fan realization the Laurent comparison is the existing product fan
isomorphism. -/
theorem projectiveLineTorusPullbackIsoLaurent_def :
    projectiveLineTorusPullbackIsoLaurent K =
      (isPullback_projectiveLineTorusProduct K).isoPullback.symm ≪≫
        projectiveLineTorusProductIsoLaurent K :=
  (rfl)

/-- The Laurent comparison preserves the projective-line projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPullbackIsoLaurent_hom_baseChangeProjection :
    (projectiveLineTorusPullbackIsoLaurent K).hom ≫ projectiveLine.baseChangeProjection K L =
      pullback.fst p t := by
  simp [projectiveLineTorusPullbackIsoLaurent]

/-- The structural map of the Laurent model reads the Laurent base projection. -/
@[reassoc (attr := simp)]
theorem projectiveLineTorusPullbackIsoLaurent_hom_toBase :
    (projectiveLineTorusPullbackIsoLaurent K).hom ≫ (projectiveLine L ↘ Spec (.of L)) =
      pullback.snd p t ≫ (projectiveLineTorusIsoSpecLaurent K).hom := by
  simp [projectiveLineTorusPullbackIsoLaurent]

/-- On both affine product charts, the inclusion of the Laurent overlap is
projective-line base change along restriction of the base coordinate. -/
@[reassoc]
theorem projectiveLineTorusProductToAffine_comp_polynomialIso (k : Fin 2) :
    projectiveLineTorusProductToAffine K k ≫ (projectiveLineAffineProductIsoPolynomial K k).hom =
      (projectiveLineTorusPullbackIsoLaurent K).hom ≫
        @projectiveLine.baseChangeProjection A _ L _
          (projectiveLineTorusToAffinePolynomial K k).toAlgebra := by
  let : Algebra A L := (projectiveLineTorusToAffinePolynomial K k).toAlgebra
  have hcoeff : algebraMap A L = projectiveLineTorusToAffinePolynomial K k :=
    RingHom.algebraMap_toAlgebra _
  let : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [hcoeff]
    simp
  apply (projectiveLine.isPullback_baseChangeProjection K A).hom_ext
  · simp
  · rw [Category.assoc, projectiveLineAffineProductIsoPolynomial_hom_toBase,
      projectiveLineTorusProductToAffine_snd_assoc, Category.assoc,
      projectiveLineTorusToAffine_algebraicMap_comp_affineFanIso,
      (projectiveLine.isPullback_baseChangeProjection A L).w,
      projectiveLineTorusPullbackIsoLaurent_hom_toBase_assoc, hcoeff]

end TauCeti.Toric.Fan
