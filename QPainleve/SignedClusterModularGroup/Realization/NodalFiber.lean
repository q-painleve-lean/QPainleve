/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.Geometry.Toric.Fan.Rationality
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical

/-!
# Geometry of marked toric fibers

The toric base has a chart isomorphic to the affine plane. The ordered internal
blowups and the projection to a marked fiber preserve its birational type.
The presentation also identifies the projection as a nodal contraction
with rational boundary normalization. For a primitive nef square-zero boundary,
the ray charges span a finite-index sublattice.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open Module (Basis)
open Scheme Scheme.IdealSheafData
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r : ℕ} {L γ : Type} [AddCommGroup L]

/-- The toric base of a complete marked presentation is rational over the ground field. -/
theorem CompleteToricPresentation.isRationalOver_fan (Q : CompleteToricPresentation i b r L γ) :
    IsRationalOver (Q.fan.algebraicRealization ↘ S) := by
  let : NeZero Q.length := Q.neZero
  obtain ⟨hdet, σ, h₀, h₁⟩ := Q.positive 0
  have hne : Q.rayOrder 0 ≠ Q.rayOrder (0 + 1) := by
    intro h
    rw [← h, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  exact Q.fan.isRationalOver_of_ray_ne_of_le Q.regular hN hne h₀ h₁

namespace CompleteToricPresentation

variable (Q : CompleteToricPresentation i b r L γ)
  {n : ℕ} [NeZero n] {H : LinearMap.BilinForm ℤ L}
  {c : GeometricRealization.Point (Over.mk (structureMap ℂ (Fin r → ℤ)))}
  {M : MarkedSurface ℂ n H (scheme ℂ (Fin r →₀ ℤ))}

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Fiber" => ContractedToricFiber
  b Q.rays Q.regular Q.cycle Q.origin Q.inclusion
  (pointsEquiv ℂ (Fin r → ℤ) (Subtype.mk (Over.Hom.left c) (Over.w c))) M

private theorem isRationalOver_fiber (p : Fiber) : IsRationalOver (M.surface ↘ S) := by
  let : IsRationalOver Q.fan.algebraicRealizationStructureMap :=
    Q.fan.algebraicRealization_over ▸ Q.isRationalOver_fan
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 Q.fan.algebraicRealizationStructureMap :=
    hN ▸ Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular
  let : IsModification p.projection := p.modification
  let c₀ := pointsEquiv ℂ (Fin r → ℤ) ⟨Over.Hom.left c, Over.w c⟩
  have hrat := (Fan.isClosedPointTower_internalBlowupTower b Q.rays
    (fun j ↦ c₀ (ofAdd (Pi.single j 1)))).isRationalOver Q.fan.algebraicRealizationStructureMap
  let : IsRationalOver (p.projection ≫ M.surface ↘ S) := p.projection_over.symm ▸ hrat
  obtain ⟨e, he⟩ := IsModification.birationalOver p.projection
  have hbir : BirationalOver (p.projection ≫ M.surface ↘ S) (M.surface ↘ S) :=
    ⟨e, by simpa only [Category.assoc, Category.comp_id] using congrArg (· ≫ M.surface ↘ S) he⟩
  exact hbir.symm.isRationalOver _ _

variable {Q} in
/-- A marked fiber with a nodal model is rational over the ground field. -/
theorem HasNodalModel.isRationalOver (h : Q.HasNodalModel c M) :
    IsRationalOver (M.surface ↘ S) := by
  obtain ⟨p, _⟩ := (Q.hasNodalModel_iff c M).mp h
  exact Q.isRationalOver_fiber p

local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {Q} in
/-- The ray charges of a marked nodal model with primitive nef square-zero boundary
span a finite-index sublattice. The model supplies rationality and the anticanonical
boundary identity at the given center. -/
theorem HasNodalModel.chargeIndex_ne_zero (h : Q.HasNodalModel c M)
    (hD : (Scheme.Hom.ker (Over.Hom.left (Arrow.hom M.pair))).IsEffectiveCartier)
    (hnef : (classOf(hD)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) :
    (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0 := by
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  obtain ⟨p, _, _, _, e, hW, hp⟩ := (Q.hasNodalModel_iff c M).mp h
  let : IsRationalOver (M.surface ↘ S) := Q.isRationalOver_fiber p
  have hcan := congrArg Inv.inv (h.canonicalClass hD)
  obtain ⟨_, _, _, _, hdiv, _, _⟩ :=
    p.chargeIndex_bounds_of_anticanonical_cycle Q.complete hW e hp.symm hD hnef hsq hcan hprim
  exact fun hz ↦ ne_zero_of_dvd_ne_zero (NeZero.ne n) hdiv (by simp [hz])

local notation "cartier" => M.isEffectiveCartier_boundaryIdeal
local notation "δ" => classOf(cartier)

variable {Q} in
/-- The exchange matrix of a marked primitive nef square-zero anticanonical
cycle is nonzero over the exponent ring `ℤ`. -/
theorem HasNodalModel.exchangeMatrix_ne_zero (h : Q.HasNodalModel c M)
    {E : SkewExchangeMatrix (Fin r)}
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M.surface δ δ = 0) :
    E.matrix ≠ 0 := by
  let P := Fan.rayChargeSeed b Q.rays hE
  exact Q.exchangeMatrix_ne_zero_of_chargeIndex_ne_zero P
    (Fan.rayChargeSeed_form _ _ _) (Fan.rayChargeSeed_charge _ _ _)
    (h.chargeIndex_ne_zero cartier hnef hsq hprim)

variable {Q} in
/-- With Cartier boundary, an ordered nodal model gives a nodal contraction,
including genus zero for every component of the boundary normalization. -/
theorem HasNodalModel.exists_isNodalContraction (h : Q.HasNodalModel c M)
    (hD : (Scheme.Hom.ker (Over.Hom.left (Arrow.hom M.pair))).IsEffectiveCartier) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃ p : Fiber, p.IsNodalContraction := by
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : PrestableFamily ((Scheme.Hom.ker (Over.Hom.left (Arrow.hom M.pair))).subscheme ↘ S) :=
    M.prestable_boundaryImage
  obtain ⟨p, Y, l, T, e, hT, hp⟩ := (Q.hasNodalModel_iff c M).mp h
  exact ⟨p, hD, h.hasToricPresentation.genus_blowupComponent_eq_zero hD,
    l, Y, T, hT, e, hp.symm⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
