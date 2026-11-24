/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Mutation.Resolution
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
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
  let j := ρ.orbitToBoundary n₂ (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have hq := ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary n₂
    (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
      (Set.mem_range_self (f := q) z)
  obtain ⟨x, hx⟩ := hq
  have hp : (D).subschemeι (j x) = (a) (IsLocalRing.closedPoint ℂ) :=
    (congrArg (fun y ↦ (D).subschemeι y) hx).trans (by
      have h := ρ.binomialCenterOnBoundary_comp_subschemeι n₂ (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c
      simpa only [Scheme.Hom.comp_apply, q] using
        congrArg (fun f : B ⟶ X ↦ f z) h)
  have : IsOpenImmersion j :=
    ρ.isOpenImmersion_orbitToBoundary n₂ (b.detDualEquiv_self _) (ρ.surjective_detCharacter b)
  have hX := Φ.smooth_algebraicRealizationStructureMap hΦ
  have hC : Smooth (j ≫ (D).subschemeι ≫ Φ.algebraicRealizationStructureMap) :=
    (ρ.smoothOfRelativeDimension_orbitToBoundary n₂ (b.detDualEquiv_self _)
      (ρ.surjective_detCharacter b)).smooth
  have := isRegularLocalRing_stalk_of_smooth Φ.algebraicRealizationStructureMap
    ((D).subschemeι (j x))
  have := (isRegularLocalRing_stalk_iff_of_isOpenImmersion j x).mpr
    (isRegularLocalRing_stalk_of_smooth (j ≫ (D).subschemeι ≫ Φ.algebraicRealizationStructureMap) x)
  rw [← hp]
  exact ((Φ.isEffectiveCartier_boundaryIdeal hΦ hc n₂).stalkOrder_eq_one_iff_isRegularLocalRing
    (j x)).mpr ‹_›

private theorem isClosed_binomialCenter :
    IsClosed ({(a) (IsLocalRing.closedPoint ℂ)} : Set X) :=
  isClosed_singleton_of_section (ρ.binomialCenter_comp_structureMap n₂ (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b) c)

private theorem isClosedPointTower_binomialCenter :
    IsClosedPointTower X (.snoc .nil (a).ker) :=
  IsClosedPointTower.nil.snoc _ (isClosed_binomialCenter b ρ c)
    (a).ker_eq_ker_fromSpecResidueField

private theorem binomialCenter_totalTransform_boundary (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    let I := (a).ker
    (D).comap I.blowupToBase =
      (I.blowupMap (D).subschemeι).ker * (I.comap I.blowupToBase) := by
  intro I
  let p := (a) (IsLocalRing.closedPoint ℂ)
  have hp : IsClosed ({p} : Set X) := isClosed_binomialCenter b ρ c
  have hI : I = vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure) :=
    (a).ker_eq_ker_fromSpecResidueField.trans (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal p)
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have hSmooth : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    (n₂) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : Smooth Φ.algebraicRealizationStructureMap := hSmooth.smooth
  have := isRegularLocalRing_stalk_of_smooth Φ.algebraicRealizationStructureMap p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    Φ.algebraicRealizationStructureMap 2).mp hSmooth).2 p hp
  rw [hI]
  have hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc n₂
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

private theorem mutationBlowupIso_totalTransform_boundary
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    (D).comap (I).blowupToBase = E * ((I).comap (I).blowupToBase) ∧
    (D').comap ((e).hom ≫ (J).blowupToBase) =
      E * ((J).comap ((e).hom ≫ (J).blowupToBase)) := by
  have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
  have hc' := (Φ.isComplete_mutationFan_iff b hv hp hOpp).mpr hc
  have hs := binomialCenter_totalTransform_boundary b ρ c hΦ hc
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have ht := binomialCenter_totalTransform_boundary b τ c⁻¹ hΨ hc'
  rw [← ρ.mutationTargetCenterIdeal_eq b hOpp c] at ht
  refine ⟨?_, ?_⟩
  · rw [← ρ.mutationSourceCenterIdeal_eq b c] at hs
    rw [Ray.ker_mutationSourceBoundaryι]
    exact hs
  · rw [comap_comp, ht, comap_mul, ρ.comap_strictBoundary_mutationBlowupIso b hOpp c hΦ,
      ← comap_comp, Ray.ker_mutationSourceBoundaryι]

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
  obtain ⟨hs, ht⟩ := mutationBlowupIso_totalTransform_boundary b ρ c hOpp hΦ hc
  have hIram := IsClosedPointTower.ramificationIdealSheafToBase_snoc ℂ hI
  have hJram := IsClosedPointTower.ramificationIdealSheafToBase_snoc ℂ hJ
  simp only [IsClosedPointTower.ramificationIdealSheafToBase_nil, comap_top, mul_top] at hIram hJram
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have := ρ.isModification_mutationSourceBlowupToBase b hOpp c
  have := ρ.isIntegral_mutationSourceBlowup b hOpp c
  have hC := (Φ.isEffectiveCartier_boundaryIdeal hΦ hc n₂).comap_of_isDominant (I).blowupToBase
  have hexceptional := (I).isEffectiveCartier_comap_blowupToBase
  have hle : (D).comap (I).blowupToBase ≤ (I).comap (I).blowupToBase := by
    rw [hs]
    exact fun _ ↦ Ideal.mul_le_right
  have hE := hC.colon hexceptional.locallyPrincipal hle
  rw [hs, hexceptional.mul_colon_cancel_right] at hE
  refine ⟨hI, hJ, hE, hs.trans ?_, ht.trans ?_⟩
  · rw [hIram]
  · rw [hJram, comap_comp]

end TauCeti.Toric.Fan
