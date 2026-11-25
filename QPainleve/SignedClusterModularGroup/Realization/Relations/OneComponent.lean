/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.SignedClusterModularGroup.Realization.Endpoint.MonomialImage
import QPainleve.SignedClusterModularGroup.Realization.Relations.Casimir

/-!
# Casimir action of the central sign for a one-component boundary

In a toric presentation of a primitive nef square-zero anticanonical cycle with
one component, Casimir exponent transport is faithful on the signed cluster
modular group. The unique point map acting by negation on the exchange kernel
is the lift of the central Picard sign change.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r : ℕ}
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M : MarkedSurface ℂ 1 B XTor[r]}
  (href : Q.HasNodalModel c M)
  (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
  (hprim : IsPrimitive (Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal)))
  (hnef : (classOf(M.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M.surface ↘ S))
  (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(M.isEffectiveCartier_boundaryIdeal)
    classOf(M.isEffectiveCartier_boundaryIdeal) = 0)

local notation "D" => M.boundaryClass M.isEffectiveCartier_boundaryIdeal
local notation "Γ" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "act" => exchangeKernelAction ℂ E
local notation "orth" => B.orthogonal (Submodule.span ℤ (Set.range D))

include href hE hprim hnef hsq in
/-- For a one-component boundary, the signed Picard equivalence identifies the
pure sign change by its action as negation on the exchange kernel. The entire
exchange-kernel action on signed cluster pullbacks is faithful and is expressed
in the charge coordinates of the marked boundary orthogonal. -/
theorem exists_picardEquiv_with_faithful_exchangeKernelAction :
    ∃ (Θ : Γ ≃* signedBoundaryIsometryGroup B D) (e : orth ≃ₗ[ℤ] E.matrix.mulVecLin.ker),
      (∀ x, (Q.inclusion x.val).2 = -(e x : Fin r → ℤ)) ∧
      (∀ g, act g = LinearEquiv.autCongr e (signedOrthogonalRestriction B D (Θ g)).val) ∧
      Function.Injective act ∧
        ∀ g : Γ, Θ g = centralSign B D (by decide) ↔ ∀ x, act g x = -x := by
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  obtain ⟨Θ, e, he, hCasimir, -, -, -, -, hcentral, -⟩ :=
    GeometricRealization.exists_exchangeKernelAction_reflection_of_presentation
      Q P rfl rfl href M.isEffectiveCartier_boundaryIdeal hprim hnef hsq
  have hinj := Q.exchangeKernelAction_injective_of_squarefree href hE hprim hnef hsq squarefree_one
  refine ⟨Θ, e, he, fun g ↦ DFunLike.congr_fun hCasimir g, hinj, fun g ↦ ⟨?_, ?_⟩⟩
  · intro hg x
    rw [← Θ.symm_apply_apply g, hg]
    exact hcentral (by decide) x
  · intro hg
    have he : act g = act (Θ.symm (centralSign B D (by decide))) :=
      LinearEquiv.ext fun x ↦ (hg x).trans (hcentral (by decide) x).symm
    rw [hinj he, Θ.apply_symm_apply]

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
