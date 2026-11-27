/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Multiplicity
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import QPainleve.Geometry.Toric.Fan.Boundary.ProjectiveLine
public import QPainleve.Geometry.Toric.Fan.Picard.FiniteFanScheme

import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# Base orders above the open orbit of a toric boundary component

A logarithmic point tower controls the total base order above the open orbit of
each boundary ray. The bound is the intersection of the original class with the
ray divisor. It includes infinitely near centers above the orbit.

See Lutz, [Proposition 8.7][HKL], for the interior-of-fiber estimate.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry LineBundleClass Chow
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.Ray

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [(Φ.finiteFanScheme K).IsProjectiveOver K]
  (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => Φ.finiteFanScheme K
local notation "S" => Spec (CommRingCat.of K)
local notation "D" => Φ.toricBoundaryIdeal K inferInstance
local notation "d₂" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "p[" c "]" => ρ.binomialCenter K d₂ (b.detDualEquiv_self ρ.primitiveGenerator)
  (ρ.surjective_detCharacter b) c (IsLocalRing.closedPoint K)

include hc in
open Classical in
/-- Selected orders above binomial points of a single ray sum to at most the degree
on that ray. The resolved line class is nef, with nonnegative orders given by the
negatives of its total exceptional coefficients. -/
theorem sum_base_orders_le_ray_degree {Y : Scheme} {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsClosedPointTower X T) :
    letI : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (Φ.finiteFanScheme_over K).symm ▸
        (d₂ ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
    (D).comap T.toBase ≤ hT.ramificationIdealSheafToBase K →
    ∀ (a : Additive (LineBundleClass X)) (m : Fin n → ℤ) (s : Finset (Fin n)),
      (∀ j, 0 ≤ m j) →
      (T.picardHom (a, -m)).toMul.IsNef K (T.toBase ≫ (X ↘ S)) →
      (∀ j ∈ s, ∃ c : Kˣ, hT.baseCenter j = p[c]) →
      ∑ j ∈ s, m j ≤
        intersectionBilinForm K X a ((Φ.rayChartDivisorToPicard K hΦ) (Pi.single ρ 1)) := by
  intro hlog a m s hm hnef hs
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
    (Φ.finiteFanScheme_over K).symm ▸
      (d₂ ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ)
  let C := Φ.rayDivisorIdeal K hΦ ρ
  let hC := Φ.isEffectiveCartier_rayDivisorIdeal K hΦ ρ
  let hD := Φ.isEffectiveCartier_boundaryIdeal K hΦ hc d₂
  have hDC : D ≤ C := Φ.boundaryIdeal_le_rayBoundaryIdeal K ρ hΦ
  let : C.subscheme.IsProjectiveOver K :=
    Scheme.IsProjectiveOver.of_isClosedImmersion K C.subschemeι
  let : TauCeti.AlgebraicGeometry.IsRegular C.subscheme := Φ.isRegular_rayBoundary K hΦ ρ
  let : C.subscheme.IsCurveOver K := ρ.isCurveOver_boundaryComponent K hΦ d₂
    (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b)
  have h := hT.sum_base_orders_le_intersection_of_logarithmic_tower hD hC hDC
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one K) hlog a.toMul m hm hnef
  have hsub : s ⊆ Finset.univ.filter
      (fun j ↦ hT.baseCenter j ∈ (C.support : Set X) \ ((D).colon C).support) := by
    intro j hj
    obtain ⟨c, hcenter⟩ := hs j hj
    rw [Finset.mem_filter, hcenter]
    exact ⟨Finset.mem_univ _, ρ.binomialCenter_mem_support_sdiff_colon K hΦ d₂
      (b.detDualEquiv_self ρ.primitiveGenerator) (ρ.surjective_detCharacter b) c⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ hm j)).trans ?_
  have := Φ.uniqueFactorizationMonoid_stalk_finiteFanScheme (R := K) hΦ
  rw [intersectionBilinForm_apply, Fan.rayChartDivisorToPicard_single, one_zsmul, toMul_ofMul,
    primeDivisorClass_def,
    mk_toInvertibleSheaf_congr _ hC (Φ.rayDivisorIdeal_def K hΦ ρ).symm]
  exact h

end TauCeti.Toric.Fan.Ray
