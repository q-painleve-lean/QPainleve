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

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.SignedClusterModularGroup.Boundary.OneComponent
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.MonomialImage
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Signed cluster relations for a one-component boundary

In a toric presentation of a primitive nef square-zero anticanonical cycle with
one component, Casimir exponent transport is faithful on the signed cluster
modular group. The unique point map acting by negation on the exchange kernel
is the lift of the central Picard sign change. Consequently, the transported
basis columns alone decide equality of signed loop pullbacks in characteristic zero.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
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
  let : Scheme.IsRationalOver (M.surface ↘ S) := href.isRationalOver
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Module.Free ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.finite_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv M.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M.picardMarking.symm.surjective
  have hB : B.Nondegenerate := M.isPerfPair_of_isRationalOver.nondegenerate
  have hpair (x y : L) : B x y =
      Chow.classIntersectionNumber ℂ M.surface (M.picardMarking x).toMul
        (M.picardMarking y).toMul :=
    (M.intersectionBilinForm_picardMarking x y).symm.trans (Chow.intersectionBilinForm_apply ..)
  have hSymm : B.IsSymm := ⟨fun x y ↦
    (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hsum : M.picardMarking (D 0) =
      Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal) := by
    rw [← M.picardMarking_sum_boundaryClass, Fintype.sum_unique]
    exact congrArg (M.picardMarking ∘ D) (Subsingleton.elim _ _)
  have hne : D 0 ≠ 0 := by
    intro h
    exact hprim.ne_zero (by simpa only [h, map_zero] using hsum.symm)
  have hself : B (D 0) (D 0) = 0 := by
    simpa only [hpair, hsum, toMul_ofMul] using hsq
  have hact (g : Γ) :
      act g = LinearEquiv.autCongr e (signedOrthogonalRestriction B D (Θ g)).val :=
    DFunLike.congr_fun hCasimir g
  have hinj : Function.Injective act := by
    intro g h he
    apply Θ.injective
    apply signedOrthogonalRestriction_injective_of_one_component hSymm hB hne hself
    apply Subtype.val_injective
    apply (LinearEquiv.autCongr e).injective
    exact (hact g).symm.trans (he.trans (hact h))
  refine ⟨Θ, e, he, hact, hinj, fun g ↦ ⟨?_, ?_⟩⟩
  · intro hg x
    rw [← Θ.symm_apply_apply g, hg]
    exact hcentral (by decide) x
  · intro hg
    have he : act g = act (Θ.symm (centralSign B D (by decide))) :=
      LinearEquiv.ext fun x ↦ (hg x).trans (hcentral (by decide) x).symm
    rw [hinj he, Θ.apply_symm_apply]

include href hE hprim hnef hsq in
/-- The transported integral basis vectors decide equality of independent X
pullbacks for a one-component boundary, over any field of characteristic zero. -/
theorem xPullback_eq_iff_exponentEquiv_eq_on_basis_of_one_component
    (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {κ : Type*} (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker) :
    w.xPullback k = v.xPullback k ↔
      ∀ j, w.exponentEquiv (β j : Fin r → ℤ) = v.exponentEquiv (β j : Fin r → ℤ) := by
  obtain ⟨_, _, _, _, hinj, -⟩ :=
    Q.exists_picardEquiv_with_faithful_exchangeKernelAction href hE hprim hnef hsq
  rw [Path.xPullback_eq_iff_ySeed_coefficient_eq k w v,
    ← Path.xPullback_eq_iff_ySeed_coefficient_eq ℂ w v]
  exact xPullback_eq_iff_exponentEquiv_eq_on_basis_of_injective ℂ E hinj w v β

include href hE hprim hnef hsq in
/-- A decision procedure for signed loop equality in a one-component presentation.
The computation takes the ambient integer coordinates of the basis as input. -/
def decidableXPullbackEqOfOneComponent
    (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {κ : Type*} [Fintype κ] (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker)
    (basisVectors : κ → Fin r → ℤ) (hb : basisVectors = fun j ↦ (β j : Fin r → ℤ)) :
    Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (∀ j, w.exponentEquiv (basisVectors j) = v.exponentEquiv (basisVectors j))
    (by
      rw [hb]
      exact (Q.xPullback_eq_iff_exponentEquiv_eq_on_basis_of_one_component
        href hE hprim hnef hsq k w v β).symm)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
