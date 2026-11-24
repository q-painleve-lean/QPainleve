/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# The common pole ideal of a toric elementary transformation

On the pivot blowup the two total boundary ideals are the same strict boundary
ideal times the respective exceptional ideals. This is the local pole comparison
for the volume-preserving elementary links in [Lutz's appendix to Hacking and
Keating, Definition 8.1 and Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry
open QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : ℂˣ)

local notation "X" => Φ.algebraicRealization
local notation "B" => Spec (CommRingCat.of ℂ)
local notation "n₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "D" => Φ.boundaryIdeal (Nonempty.intro (Ray.toCone Φ ρ))
local notation "a" =>
  Ray.binomialCenter ρ n₂ (Basis.detDualEquiv_self b ρ.primitiveGenerator)
    (Ray.surjective_detCharacter ρ b) c

private theorem stalkOrder_boundary_binomialCenter (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    (D).stalkOrder ((a) (IsLocalRing.closedPoint ℂ)) = 1 := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let z : B := IsLocalRing.closedPoint ℂ
  let q := ρ.binomialCenterOnBoundary n₂ (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  have hp : (D).subschemeι (q z) = (a) z := by
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : B ⟶ X ↦ f z)
      (ρ.binomialCenterOnBoundary_comp_subschemeι n₂ (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c)
  have hq : q z ∈ (ρ.internalCenter b c).val.support := by
    rw [Ray.internalCenter_val]
    exact q.range_subset_ker_support (Set.mem_range_self z)
  have : Smooth Φ.algebraicRealizationStructureMap := Φ.smooth_algebraicRealizationStructureMap hΦ
  have := isRegularLocalRing_stalk_of_smooth Φ.algebraicRealizationStructureMap
    ((D).subschemeι (q z))
  rw [← hp]
  exact ((Φ.isEffectiveCartier_boundaryIdeal hΦ hc n₂).stalkOrder_eq_one_iff_isRegularLocalRing
    (q z)).mpr (ρ.isRegularLocalRing_stalk_of_mem_support_internalCenter b c hq)

private theorem isClosed_binomialCenter :
    IsClosed ({(a) (IsLocalRing.closedPoint ℂ)} : Set X) :=
  isClosed_singleton_of_section (ρ.binomialCenter_comp_structureMap n₂ (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b) c)

private theorem isClosedPointTower_binomialCenter :
    IsClosedPointTower X (.snoc .nil (a).ker) :=
  IsClosedPointTower.nil.snoc _ (isClosed_binomialCenter b ρ c)
    (a).ker_eq_ker_fromSpecResidueField

private theorem binomialCenter_boundary_transforms (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    let I := (a).ker
    let S := (I.blowupMap (D).subschemeι).ker
    S.IsEffectiveCartier ∧ (D).comap I.blowupToBase = S * (I.comap I.blowupToBase) := by
  intro I
  let p := (a) (IsLocalRing.closedPoint ℂ)
  have hp : IsClosed ({p} : Set X) := isClosed_binomialCenter b ρ c
  have hI : I = vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure) :=
    (a).ker_eq_ker_fromSpecResidueField.trans (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal p)
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have hSmooth : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    (n₂) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : Smooth Φ.algebraicRealizationStructureMap := hSmooth.smooth
  have : IsNoetherian X := isNoetherian_of_finiteType Φ.algebraicRealizationStructureMap
  have := isRegularLocalRing_stalk_of_smooth Φ.algebraicRealizationStructureMap p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    Φ.algebraicRealizationStructureMap 2).mp hSmooth).2 p hp
  rw [hI]
  have hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc n₂
  refine ⟨hD.strictTransform_pointBlowup hp hdim, ?_⟩
  simpa only [p, stalkOrder_boundary_binomialCenter b ρ c hΦ hc, ENat.toNat_one, pow_one] using
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim

variable (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "D'" =>
  Fan.boundaryIdeal Ψ (Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone))
local notation "I" => Ray.mutationSourceCenterIdeal b ρ c
local notation "J" => Ray.mutationTargetCenterIdeal b ρ hOpp c
local notation "e" => Ray.mutationBlowupIso b ρ hOpp c
local notation "E" => Scheme.Hom.ker (ρ.mutationSourceBoundaryι b c)

private theorem mutationBlowupIso_boundary_transforms
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    (E).IsEffectiveCartier ∧
    (D).comap (I).blowupToBase = E * ((I).comap (I).blowupToBase) ∧
    (D').comap ((e).hom ≫ (J).blowupToBase) =
      E * ((J).comap ((e).hom ≫ (J).blowupToBase)) := by
  have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
  have hc' := (Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc
  obtain ⟨hE, hs⟩ := binomialCenter_boundary_transforms b ρ c hΦ hc
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have ht := (binomialCenter_boundary_transforms b τ c⁻¹ hΨ hc').2
  rw [← ρ.mutationSourceCenterIdeal_eq b c] at hE hs
  rw [← ρ.mutationTargetCenterIdeal_eq b hOpp c] at ht
  rw [Ray.ker_mutationSourceBoundaryι]
  refine ⟨hE, hs, ?_⟩
  rw [comap_comp, ht, comap_mul, ρ.comap_strictBoundary_mutationBlowupIso b hOpp c hΦ,
    ← comap_comp]

local notation "X'" => Fan.algebraicRealization Ψ

/-- The strict boundary of the source pivot blowup is effective Cartier and serves as
the common pole ideal. Pulling back either reduced toric boundary gives this ideal
times the ramification ideal of the corresponding projection, with the target
ramification pulled back along the pivot isomorphism. -/
theorem Ray.mutationBlowupIso_pole_ideal (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    let : SmoothOfRelativeDimension 2 (X ↘ B) := by
      rw [Fan.algebraicRealization_over]
      exact (n₂) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 (X' ↘ B) := by
      rw [Fan.algebraicRealization_over]
      have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
      exact (n₂) ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    ∃ (hI : IsClosedPointTower X (.snoc .nil I))
      (hJ : IsClosedPointTower X' (.snoc .nil J)),
      (E).IsEffectiveCartier ∧
      (D).comap (I).blowupToBase = E * hI.ramificationIdealSheafToBase ℂ ∧
      (D').comap ((e).hom ≫ (J).blowupToBase) =
        E * ((hJ.ramificationIdealSheafToBase ℂ).comap (e).hom) := by
  intro _ _
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have hI := isClosedPointTower_binomialCenter b ρ c
  have hJ := isClosedPointTower_binomialCenter b τ c⁻¹
  rw [← ρ.mutationSourceCenterIdeal_eq b c] at hI
  rw [← ρ.mutationTargetCenterIdeal_eq b hOpp c] at hJ
  obtain ⟨hE, hs, ht⟩ := mutationBlowupIso_boundary_transforms b ρ c hOpp hΦ hc
  have hIram := IsClosedPointTower.ramificationIdealSheafToBase_snoc ℂ hI
  have hJram := IsClosedPointTower.ramificationIdealSheafToBase_snoc ℂ hJ
  simp only [IsClosedPointTower.ramificationIdealSheafToBase_nil, comap_top, mul_top] at hIram hJram
  refine ⟨hI, hJ, hE, hs.trans ?_, ht.trans ?_⟩
  · rw [hIram]
  · rw [hJram, comap_comp]

end TauCeti.Toric.Fan
