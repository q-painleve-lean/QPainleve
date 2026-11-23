/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Complexity
public import QPainleve.Geometry.Toric.Fan.InternalBlowup
public import QPainleve.Geometry.Toric.Fan.Picard.Rank

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import QPainleve.Geometry.Toric.Fan.Boundary.StrictTransform
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# The number of internal centers in a toric presentation

Boundary complexity counts the internal centers of any ordered toric presentation,
including repeated centers. The toric Picard sequence gives the starting rank,
and the Picard marking adds one coordinate per internal blowup. The strict ray
divisors account for all boundary primes. Nodal blowups preserve complexity,
so the count also holds on the original surface.

See Friedman, *On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2, for
the charge and its behavior under internal and corner blowups.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "D" => Φ.boundaryIdeal inferInstance
local notation "P" => internalBlowupTower b s c
local notation "B" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd P))
local notation "J" => (fun j ↦ Ray.internalCenter b (s j) (c j))
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "f" => Φ.algebraicRealizationStructureMap

include hΦ in
/-- The strict-transform boundary of the ordered internal blowup model has one prime
for each original ray, including when some centers are infinitely near. -/
theorem ncard_boundaryPrimes_internalBlowupTower :
    (B).boundaryPrimes.ncard = Nat.card Φ.Ray := by
  rw [internalBlowupTower_eq_alongBoundary]
  let P' := alongBoundary (D).subschemeι J
  let j := (Sigma.snd P').boundaryι
  let g (ρ : Φ.Ray) := ρ.boundaryComponentι hΦ ≫ j
  let S (ρ : Φ.Ray) := Φ.rayBoundaryIdeal hΦ ρ
  let (ρ : Φ.Ray) : IsIntegral (S ρ).subscheme := by
    simp only [S, rayBoundaryIdeal_def]
    exact isIntegral_subscheme_vanishingIdeal (isIrreducible_singleton.closure)
  have hg (ρ : Φ.Ray) : (g ρ).ker = strictTransform (S ρ) (Sigma.snd P').toTower :=
    (strictTransform_rayBoundaryIdeal_alongBoundary hΦ J ρ
      (fun t ↦ (s t).isEffectiveCartier_comap_internalCenter b (c t) hΦ ρ)).symm
  have : IsNoetherian P'.1 := (Sigma.snd P').toTower.isNoetherian
  let (ρ : Φ.Ray) : IsIntegral (g ρ).ker.subscheme :=
    IsIntegral.of_isIso (g ρ).toImage
  have hC (ρ : Φ.Ray) : (g ρ).ker.IsEffectiveCartier := by
    rw [hg]
    have : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    have hT := isClosedPointTower_internalBlowupTower b s c
    rw [internalBlowupTower_eq_alongBoundary] at hT
    exact hT.isEffectiveCartier_strictTransform f (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ)
  let η (ρ : Φ.Ray) : CodimensionOnePoint P'.1 :=
    ⟨(g ρ).ker.subschemeι (genericPoint (g ρ).ker.subscheme),
      (hC ρ).coheight_subschemeι_genericPoint⟩
  have hη (ρ : Φ.Ray) : (η ρ : P'.1) = g ρ (genericPoint (S ρ).subscheme) := by
    -- The image isomorphism identifies the two generic points of the ray divisor.
    change (g ρ).ker.subschemeι (genericPoint (g ρ).ker.subscheme) = _
    rw [← (g ρ).toImage.genericPoint_eq_of_isDominant, ← Scheme.Hom.comp_apply,
      Scheme.Hom.toImage_imageι]
  -- Projection to the original surface sends the image prime to its original ray prime.
  have hbase (ρ : Φ.Ray) :
      (Sigma.snd P').toTower.toBase (η ρ : P'.1) = (Φ.rayBoundaryPoint hΦ ρ : _) := by
    rw [hη, ← Scheme.Hom.comp_apply]
    simp only [g, j, Category.assoc, WithBoundary.boundaryι_toBase,
      Ray.boundaryComponentι_subschemeι]
    symm
    apply (Φ.isEffectiveCartier_rayBoundaryIdeal hΦ ρ).mem_support_iff_eq_subschemeι_genericPoint
      (Φ.rayBoundaryPoint hΦ ρ).property |>.mp
    rw [← SetLike.mem_coe, coe_support_rayBoundaryIdeal]
    exact subset_closure (Set.mem_singleton _)
  apply ncard_boundaryPrimes_eq_of_iUnion_closure _ η
  · intro ρ τ h
    apply Φ.rayBoundaryPoint_injective hΦ
    apply Subtype.ext
    simpa only [hbase] using congrArg
      (fun q : CodimensionOnePoint P'.1 ↦ (Sigma.snd P').toTower.toBase (q : P'.1)) h
  · rw [support_ker_alongBoundary_boundaryι hΦ J
      (fun t ρ ↦ (s t).isEffectiveCartier_comap_internalCenter b (c t) hΦ ρ)]
    exact Set.iUnion_congr fun ρ ↦ by
      rw [← hg]
      exact (g ρ).ker.support_eq_closure_subschemeι_genericPoint

include hΦ in
/-- The boundary complexity of the ordered toric blowup model equals its number of centers. -/
theorem boundaryComplexity_internalBlowupTower (hc : Φ.IsComplete) :
    (B).boundaryComplexity = (n : ℤ) := by
  have h := finrank_picard_add_finrank_eq_natCard_ray hΦ hc
  rw [rankTwo] at h
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (.of ℂ)) := by
    rw [algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let := Fintype.ofFinite Φ.Ray
  let : Module.Finite ℤ (Additive (LineBundleClass Φ.algebraicRealization)) :=
    Module.Finite.of_surjective (Φ.rayDivisorToPicard hΦ).toIntLinearMap
      (Φ.rayDivisorToPicard_surjective hΦ)
  rw [boundaryComplexity_def, ncard_boundaryPrimes_internalBlowupTower hΦ b s c,
    finrank_picard ℂ (isClosedPointTower_internalBlowupTower b s c), ← h]
  push_cast
  ring

variable {X Y : Scheme} [IsNoetherian X] [IsIntegral X] [X.Over (Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [Module.Finite ℤ (Additive (LineBundleClass X))]
  {A : X.IdealSheafData} {d : ℕ} {U : QPainleve.BlowupTower X d Y}

include hΦ in
/-- The complexity of a pair with a specified toric presentation counts its internal
centers. The nodal tower and the internal tower may each be empty. -/
theorem boundaryComplexity_eq_length_of_toricPresentation (hc : Φ.IsComplete)
    (hA : A.IsEffectiveCartier)
    (hU : IsNodalBoundaryTower A (X ↘ Spec (.of ℂ)) (𝟙 X) U)
    (e : Y ≅ (P).1) (he : ((A.comap U.toBase).comap e.inv).support = (B).support) :
    A.boundaryComplexity = (n : ℤ) := by
  calc
    _ = (A.comap U.toBase).boundaryComplexity := (hU.boundaryComplexity_comap hA).symm
    _ = ((A.comap U.toBase).comap e.inv).boundaryComplexity :=
      (boundaryComplexity_comap_iso e.symm _).symm
    _ = (B).boundaryComplexity := boundaryComplexity_eq_of_support_eq he
    _ = _ := boundaryComplexity_internalBlowupTower hΦ b s c hc

end TauCeti.Toric.Fan
