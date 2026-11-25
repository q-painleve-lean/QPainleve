/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.CurveIntersection
public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.Picard.Presentation
public import QPainleve.Geometry.Toric.Fan.Smooth

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine

/-!
# First base orders on a toric boundary curve

The intersection with a ray divisor bounds the sum of the orders at first centers
on that divisor. The bound includes centers at toric fixed points and applies
to any closed-point tower with a nef resolved class.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass Chow
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.Ray

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)

local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Φ.rayBoundaryIdeal hΦ ρ
local notation "d₂" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)

open Classical in
/-- The orders of selected first centers on a ray divisor sum to at most its
intersection with the base part of the nef class. The orders are the negatives
of the total exceptional coordinates. Centers at either endpoint of the ray's
open orbit are included. -/
theorem sum_first_base_orders_le_ray_degree {Y : Scheme} {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) (a : Additive (LineBundleClass X)) (m : Fin n → ℕ)
    (s : Finset (Fin n))
    (hs : ∀ j ∈ s, hT.baseCenter j ∈ (C).support ∧
      ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hnef : (T.picardHom (a, fun j ↦ -(m j : ℤ))).toMul.IsNef ℂ (T.toBase ≫ (X ↘ S))) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      rw [Fan.algebraicRealization_over]
      exact d₂ ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    ∑ j ∈ s, (m j : ℤ) ≤
      intersectionBilinForm ℂ X a ((Φ.rayDivisorToPicard hΦ) (Pi.single ρ 1)) := by
  intro hdim
  let := hdim
  let : TauCeti.AlgebraicGeometry.IsRegular (C).subscheme := Φ.isRegular_rayBoundary hΦ ρ
  let : (C).subscheme.IsCurveOver ℂ := ρ.isCurveOver_boundaryComponent hΦ d₂
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b)
  have hC := Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hdimX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hpair := classIntersectionNumber_eq_intersectionNumber_subschemeι
    ℂ hdimX.le hC (Scheme.IsCurveOver.topologicalKrullDim_eq_one ℂ) a.toMul
  rw [intersectionBilinForm_apply, Fan.rayDivisorToPicard_single, one_zsmul, toMul_ofMul,
    primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ hC (Φ.rayBoundaryIdeal_def hΦ ρ).symm, hpair]
  exact hT.sum_first_base_orders_le_curve_intersection (C).subschemeι (X ↘ S) rfl
    a.toMul m s (fun j hj ↦ ⟨(C).range_subschemeι.symm ▸ (hs j hj).1, (hs j hj).2⟩)
    (by simpa only [ofMul_toMul] using hnef)

end TauCeti.Toric.Fan.Ray
