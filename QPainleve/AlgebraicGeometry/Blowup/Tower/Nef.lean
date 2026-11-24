/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Nef classes in ordered point-blowup coordinates

The base coordinate of a nef class is nef, and each total-transform exceptional
coordinate is nonpositive. If a base divisor contains the projected center, its
intersection with the base class bounds the negative exceptional coefficient.
This follows by subtracting the total exceptional divisor from the total transform
of the base divisor.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Chow
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

section Projective

variable [IsAlgClosed k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)

/-- The base part of a nef line-bundle class in the point-blowup marking is nef.
Intersection with the effective total transform of a prime divisor tests the
degree of this base part on that divisor. -/
theorem isNef_fst_of_isNef_picardHom (hT : IsClosedPointTower X T)
    {a : Additive (LineBundleClass X) × (Fin n → ℤ)}
    (ha : (T.picardHom a).toMul.IsNef k (T.toBase ≫ f)) :
    a.1.toMul.IsNef k f := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : IsIntegral Y := hT.isIntegral f
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  have := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  apply (isNef_iff_classIntersectionNumber_nonneg k hX _).mpr
  intro p
  let D := vanishingIdeal (X := X) ⟨closure {(p : X)}, isClosed_closure⟩
  have hD : D.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have hE := hT.isEffectiveCartier_totalTransform f hD
  have h := classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hY ha hE
  have hclass : primeDivisorClass p = (mk hD.toInvertibleSheaf)⁻¹ := primeDivisorClass_def p
  have hpair :=
    classIntersectionNumber_picardMarking k hT a (Additive.ofMul (primeDivisorClass p), 0)
  simp only [picardMarking_apply, picardHom_apply_zero, toMul_ofMul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, sub_zero] at hpair
  rw [← hD.pullback_mk_toInvertibleSheaf hE, ← pullback_inv, ← hclass, hpair] at h
  exact h

/-- Each exceptional coefficient of a nef class in the point-blowup marking is
nonpositive, even if the total transform of the corresponding exceptional curve
is reducible. -/
theorem exceptionalCoeff_nonpos_of_isNef_picardHom (hT : IsClosedPointTower X T)
    {a : Additive (LineBundleClass X) × (Fin n → ℤ)}
    (ha : (T.picardHom a).toMul.IsNef k (T.toBase ≫ f)) (j : Fin n) :
    a.2 j ≤ 0 := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : IsIntegral Y := hT.isIntegral f
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  have := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  obtain ⟨D, hD, hclass, -⟩ := hT.exists_isEffectiveCartier_exceptionalClass f j
  have h := classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hY ha hD
  rw [hclass, classIntersectionNumber_picardHom_exceptionalClass hT] at h
  exact neg_nonneg.mp h

/-- The intersection of the base part of a nef class with an effective Cartier divisor
through a projected center bounds the negative of the corresponding exceptional coefficient.
The center can be infinitely near. -/
theorem neg_exceptionalCoeff_le_classIntersectionNumber_of_mem_support
    (hT : IsClosedPointTower X T) {a : Additive (LineBundleClass X) × (Fin n → ℤ)}
    (ha : (T.picardHom a).toMul.IsNef k (T.toBase ≫ f)) (j : Fin n)
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) (hj : hT.baseCenter j ∈ D.support) :
    -a.2 j ≤ classIntersectionNumber k X a.1.toMul (mk hD.toInvertibleSheaf)⁻¹ := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : IsIntegral Y := hT.isIntegral f
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f
  have := (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  obtain ⟨E, hE, hExc, hle⟩ := hT.exists_isEffectiveCartier_exceptionalClass f j
  have hTotal := hT.isEffectiveCartier_totalTransform f hD
  obtain ⟨R, hR, hProd⟩ := (hTotal.le_iff_exists_eq_mul hE.locallyPrincipal).mp (hle D hj)
  have hClass := (mk_toInvertibleSheaf_congr hTotal
    (TauCeti.isEffectiveCartier_mul hR hE) hProd).trans (mk_toInvertibleSheaf_mul hR hE)
  have hBound := classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier k hY ha hR
  have hPair := classIntersectionNumber_picardMarking k hT a
    (Additive.ofMul (mk hD.toInvertibleSheaf)⁻¹, 0)
  simp only [picardMarking_apply, picardHom_apply_zero, toMul_ofMul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, sub_zero] at hPair
  rw [pullback_inv, hD.pullback_mk_toInvertibleSheaf hTotal, hClass, mul_inv_rev,
    classIntersectionNumber_mul_right k hY, hExc,
    classIntersectionNumber_picardHom_exceptionalClass hT] at hPair
  omega

end Projective

end QPainleve.BlowupTower.IsClosedPointTower
