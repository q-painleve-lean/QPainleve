/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.Geometry.Toric.Fan.Mutation.Boundary

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Boundary.Node
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

variable (K : Type) [Field K] {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : Kˣ)

local notation "X" => Φ.finiteFanScheme K
local notation "B" => Spec (CommRingCat.of K)
local notation "n₂" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "D" => Φ.toricBoundaryIdeal K (Nonempty.intro (Ray.toCone Φ ρ))
local notation "a" =>
  Ray.binomialCenter ρ K n₂ (Basis.detDualEquiv_self b ρ.primitiveGenerator)
    (Ray.surjective_detCharacter ρ b) c

private theorem stalkOrder_boundary_binomialCenter (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    (D).stalkOrder ((a) (IsLocalRing.closedPoint K)) = 1 := by
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  let z : B := IsLocalRing.closedPoint K
  let q := ρ.binomialCenterOnBoundary K n₂ (b.detDualEquiv_self _) (ρ.surjective_detCharacter b) c
  have hp : (D).subschemeι (q z) = (a) z := by
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : B ⟶ X ↦ f z)
      (ρ.binomialCenterOnBoundary_comp_subschemeι K n₂ (b.detDualEquiv_self _)
        (ρ.surjective_detCharacter b) c)
  have hq : q z ∈ (ρ.internalCenter K b c).val.support := by
    rw [Ray.internalCenter_val]
    exact q.range_subset_ker_support (Set.mem_range_self z)
  have : Smooth (Φ.finiteFanSchemeToSpec K) :=
    (Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ).smooth
  have := isRegularLocalRing_stalk_of_smooth (Φ.finiteFanSchemeToSpec K)
    ((D).subschemeι (q z))
  rw [← hp]
  exact ((Φ.isEffectiveCartier_boundaryIdeal K hΦ hc n₂).stalkOrder_eq_one_iff_isRegularLocalRing
    (q z)).mpr (ρ.isRegularLocalRing_stalk_of_mem_support_internalCenter K b c hq)

private theorem isClosed_binomialCenter :
    IsClosed ({(a) (IsLocalRing.closedPoint K)} : Set X) :=
  isClosed_singleton_of_section (ρ.binomialCenter_comp_structureMap K n₂ (b.detDualEquiv_self _)
    (ρ.surjective_detCharacter b) c)

private theorem isClosedPointTower_binomialCenter :
    IsClosedPointTower X (.snoc .nil (a).ker) :=
  IsClosedPointTower.nil.snoc _ (isClosed_binomialCenter K b ρ c)
    (a).ker_eq_ker_fromSpecResidueField

private theorem binomialCenter_boundary_transforms (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    let I := (a).ker
    let S := (I.blowupMap (D).subschemeι).ker
    S.IsEffectiveCartier ∧ (D).comap I.blowupToBase = S * (I.comap I.blowupToBase) := by
  intro I
  let p := (a) (IsLocalRing.closedPoint K)
  have hp : IsClosed ({p} : Set X) := isClosed_binomialCenter K b ρ c
  have hI : I = vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure) :=
    (a).ker_eq_ker_fromSpecResidueField.trans (Scheme.ker_fromSpecResidueField_eq_vanishingIdeal p)
  let : Nonempty Φ.cones := ⟨ρ.toCone⟩
  have hSmooth : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    (n₂) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  have : Smooth (Φ.finiteFanSchemeToSpec K) := hSmooth.smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (Φ.finiteFanSchemeToSpec K)
  have := isRegularLocalRing_stalk_of_smooth (Φ.finiteFanSchemeToSpec K) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
    (Φ.finiteFanSchemeToSpec K) 2).mp hSmooth).2 p hp
  rw [hI]
  have hD := Φ.isEffectiveCartier_boundaryIdeal K hΦ hc n₂
  refine ⟨hD.strictTransform_pointBlowup hp hdim, ?_⟩
  simpa only [p, stalkOrder_boundary_binomialCenter K b ρ c hΦ hc, ENat.toNat_one, pow_one] using
    hD.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim

variable (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "D'" =>
  Fan.toricBoundaryIdeal K Ψ (Nonempty.intro (Φ.mutationFanConeEquiv b hv hp hOpp ρ.toCone))
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
  obtain ⟨hE, hs⟩ := binomialCenter_boundary_transforms K b ρ c hΦ hc
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have ht := (binomialCenter_boundary_transforms K b τ c⁻¹ hΨ hc').2
  rw [← ρ.mutationSourceCenterIdeal_eq b c] at hE hs
  rw [← ρ.mutationTargetCenterIdeal_eq b hOpp c] at ht
  rw [Ray.ker_mutationSourceBoundaryι]
  refine ⟨hE, hs, ?_⟩
  rw [comap_comp, ht, comap_mul, ρ.comap_strictBoundary_mutationBlowupIso b hOpp c hΦ,
    ← comap_comp]

local notation "X'" => Fan.finiteFanScheme K Ψ

/-- The strict boundary of the source pivot blowup is effective Cartier and serves as
the common pole ideal. Pulling back either reduced toric boundary gives this ideal
times the ramification ideal of the corresponding projection, with the target
ramification pulled back along the pivot isomorphism. -/
theorem Ray.mutationBlowupIso_pole_ideal [PerfectField K] (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    let : SmoothOfRelativeDimension 2 (X ↘ B) := by
      rw [Fan.finiteFanScheme_over]
      exact (n₂) ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
    let : SmoothOfRelativeDimension 2 (X' ↘ B) := by
      rw [Fan.finiteFanScheme_over]
      have hΨ := (Φ.isRegular_mutationFan_iff b hv hp hOpp).mpr hΦ
      exact (n₂) ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec K hΨ
    ∃ (hI : IsClosedPointTower X (.snoc .nil I))
      (hJ : IsClosedPointTower X' (.snoc .nil J)),
      (E).IsEffectiveCartier ∧
      (D).comap (I).blowupToBase = E * hI.ramificationIdealSheafToBase K ∧
      (D').comap ((e).hom ≫ (J).blowupToBase) =
        E * ((hJ.ramificationIdealSheafToBase K).comap (e).hom) := by
  intro _ _
  let τ := Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
  have hI := isClosedPointTower_binomialCenter K b ρ c
  have hJ := isClosedPointTower_binomialCenter K b τ c⁻¹
  rw [← ρ.mutationSourceCenterIdeal_eq b c] at hI
  rw [← ρ.mutationTargetCenterIdeal_eq b hOpp c] at hJ
  obtain ⟨hE, hs, ht⟩ := mutationBlowupIso_boundary_transforms K b ρ c hOpp hΦ hc
  have hIram := IsClosedPointTower.ramificationIdealSheafToBase_snoc K hI
  have hJram := IsClosedPointTower.ramificationIdealSheafToBase_snoc K hJ
  simp only [IsClosedPointTower.ramificationIdealSheafToBase_nil, comap_top, mul_top] at hIram hJram
  refine ⟨hI, hJ, hE, hs.trans ?_, ht.trans ?_⟩
  · rw [hIram]
  · rw [hJram, comap_comp]

end TauCeti.Toric.Fan
