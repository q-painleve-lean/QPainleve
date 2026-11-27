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

import QPainleve.SignedClusterModularGroup.Realization.Presentation.Casimir
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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀] [CharZero k₀]

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r : ℕ}
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation k₀ i b r L γ)
  {c : Point (Over.mk (QPainleve.CharacterTorus.structureMap k₀ (Fin r →
    ℤ)))} {M : MarkedSurface k₀ 1 B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}
  (href : Q.HasNodalModel c M)
  (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
  (hprim : IsPrimitive (Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal)))
  (hnef : (classOf(M.isEffectiveCartier_boundaryIdeal)).IsNef k₀ (M.surface ↘ Spec (.of k₀)))
  (hsq : Chow.classIntersectionNumber k₀ M.surface classOf(M.isEffectiveCartier_boundaryIdeal)
    classOf(M.isEffectiveCartier_boundaryIdeal) = 0)

local notation "D" => M.boundaryClass M.isEffectiveCartier_boundaryIdeal
local notation "Γ" => (SignedClusterModularGroup k₀ E)ᵐᵒᵖ
local notation "act" => exchangeKernelAction k₀ E
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
  obtain ⟨A⟩ := Q.nonempty_casimirActionComparison_of_nodal_model href hE hprim hnef hsq
  have hcentral := GeometricRealization.exchangeKernelAction_picardEquiv_symm_centralSign
    A.exchangeKernelAction_eq (by decide : 1 ≤ 2)
  have hinj := Q.exchangeKernelAction_injective_of_squarefree
    href hE hprim hnef hsq squarefree_one k₀
  refine ⟨A.picardEquiv, A.exchangeKernelEquiv,
    fun x ↦ neg_eq_iff_eq_neg.mp (A.coe_exchangeKernelEquiv_apply x).symm,
    A.exchangeKernelAction_apply, hinj, fun g ↦ ⟨?_, ?_⟩⟩
  · intro hg x
    rw [← A.picardEquiv.symm_apply_apply g, hg]
    exact hcentral x
  · intro hg
    have he : act g = act (A.picardEquiv.symm (centralSign B D (by decide))) :=
      LinearEquiv.ext fun x ↦ (hg x).trans (hcentral x).symm
    rw [hinj he, A.picardEquiv.apply_symm_apply]

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
