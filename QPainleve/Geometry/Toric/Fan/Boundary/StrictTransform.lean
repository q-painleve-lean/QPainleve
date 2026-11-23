/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform
public import QPainleve.Geometry.Toric.Fan.Boundary.Component
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

/-!
# Boundary components of ordered toric blowups

Each ray divisor embeds into the final surface through the fixed reduced boundary.
Its image is the scheme-theoretic strict transform, and these images cover the
final boundary. This includes repeated centers on the same ray.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular)

local notation "toricBoundary" => Φ.boundaryIdeal inferInstance

variable (J : Fin n →
  {K : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // K.IsEffectiveCartier})

local notation "model" => alongBoundary (subschemeι toricBoundary) J
local notation "strictIdeal" ρ:arg => strictTransform (Φ.rayBoundaryIdeal hΦ ρ)
  (WithBoundary.toTower (Sigma.snd model))

/-- The closed embedding of an original ray divisor through the fixed reduced boundary
defines its strict transform in the final surface if each center restricts to a Cartier
ideal on that ray. -/
theorem strictTransform_rayBoundaryIdeal_alongBoundary (ρ : Φ.Ray)
    (hρ : ∀ j, ((J j).val.comap (ρ.boundaryComponentι hΦ)).IsEffectiveCartier) :
    strictIdeal ρ = (ρ.boundaryComponentι hΦ ≫ (model).2.boundaryι).ker := by
  simpa only [Ray.boundaryComponentι_subschemeι, ker_subschemeι] using
    strictTransform_ker_comp_alongBoundary (toricBoundary).subschemeι (ρ.boundaryComponentι hΦ) J hρ

/-- Each strict transform of a toric ray divisor in the ordered blowup model is integral. -/
theorem isIntegral_strictTransform_rayBoundaryIdeal (ρ : Φ.Ray)
    (hρ : ∀ j, ((J j).val.comap (ρ.boundaryComponentι hΦ)).IsEffectiveCartier) :
    IsIntegral (strictIdeal ρ).subscheme := by
  have : IsIntegral (Φ.rayBoundaryIdeal hΦ ρ).subscheme := by
    rw [rayBoundaryIdeal_def]
    exact isIntegral_subscheme_vanishingIdeal (isIrreducible_singleton.closure)
  rw [strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ hρ]
  exact IsIntegral.of_isIso (ρ.boundaryComponentι hΦ ≫ (model).2.boundaryι).toImage

/-- The reduced boundary of the ordered model is supported on the union of its strict
ray divisors. -/
theorem support_ker_alongBoundary_boundaryι
    (hJ : ∀ j (ρ : Φ.Ray), ((J j).val.comap (ρ.boundaryComponentι hΦ)).IsEffectiveCartier) :
    ((model).2.boundaryι.ker.support : Set (model).1) =
      ⋃ ρ : Φ.Ray, ((strictIdeal ρ).support : Set (model).1) := by
  let j := (model).2.boundaryι
  rw [j.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_univ (f := j),
    ← iUnion_range_boundaryComponentι hΦ, Set.image_iUnion]
  refine Set.iUnion_congr fun ρ ↦ ?_
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ (fun j ↦ hJ j ρ)]
  let k := ρ.boundaryComponentι hΦ ≫ j
  exact (k.support_ker.trans k.isClosedEmbedding.isClosed_range.closure_eq).symm

/-- The ray component embedded through the fixed boundary is the strict transform of
the ray divisor in the ordered internal model. -/
theorem ker_boundaryComponentι_internalBlowupTower
    (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
    (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    (ρ.boundaryComponentι hΦ ≫ (internalBlowupTower b s c).2.boundaryι).ker =
      strictTransform (Φ.rayBoundaryIdeal hΦ ρ) (internalBlowupTower b s c).2.toTower := by
  let D := (Φ.boundaryIdeal inferInstance).subschemeι
  let J (k : Fin n) := (s k).internalCenter b (c k)
  let P (M : Σ Z, WithBoundary D n Z) :=
    (ρ.boundaryComponentι hΦ ≫ M.2.boundaryι).ker =
      strictTransform (Φ.rayBoundaryIdeal hΦ ρ) M.2.toTower
  apply (congrArg P (internalBlowupTower_eq_alongBoundary b s c)).mpr
  exact (strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ
    (fun k ↦ (s k).isEffectiveCartier_comap_internalCenter b (c k) hΦ ρ)).symm

/-- The boundary of the ordered internal model is supported on the union of the
strict transforms of the ray divisors, also for repeated centers. -/
theorem support_ker_internalBlowupTower_boundaryι
    (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)
    (hΦ : Φ.IsRegular) :
    ((internalBlowupTower b s c).2.boundaryι.ker.support : Set (internalBlowupTower b s c).1) =
      ⋃ ρ : Φ.Ray, (strictTransform (Φ.rayBoundaryIdeal hΦ ρ)
        (internalBlowupTower b s c).2.toTower).support := by
  rw [internalBlowupTower_eq_alongBoundary]
  exact support_ker_alongBoundary_boundaryι hΦ _
    (fun k ρ ↦ (s k).isEffectiveCartier_comap_internalCenter b (c k) hΦ ρ)

end TauCeti.Toric.Fan
