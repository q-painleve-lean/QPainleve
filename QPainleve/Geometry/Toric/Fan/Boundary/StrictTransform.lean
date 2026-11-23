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
  have hcover : (⋃ ρ : Φ.Ray, Set.range (ρ.boundaryComponentι hΦ)) = Set.univ := by
    apply Set.image_injective.mpr (toricBoundary).subschemeι.isClosedEmbedding.injective
    rw [Set.image_iUnion, Set.image_univ]
    simp only [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      Ray.boundaryComponentι_subschemeι, range_subschemeι, coe_support_rayBoundaryIdeal]
    exact (Φ.support_boundaryIdeal_eq_iUnion_closure hΦ inferInstance).symm
  let j := (model).2.boundaryι
  rw [j.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq, ← Set.image_univ (f := j),
    ← hcover, Set.image_iUnion]
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
  refine (strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ ?_).symm
  intro k
  rw [Ray.internalCenter_val]
  exact (s k).isEffectiveCartier_comap_ker_binomialCenterOnBoundary hΦ
    (by simpa using Module.finrank_eq_card_basis b) (b.detDualEquiv_self _)
    ((s k).surjective_detCharacter b) (c k) ρ

end TauCeti.Toric.Fan
