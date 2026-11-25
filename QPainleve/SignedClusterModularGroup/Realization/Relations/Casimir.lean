/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Nat.Squarefree
public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.SignedClusterModularGroup.Boundary.RotationKernel
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.MonomialImage
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import TauCeti.LinearAlgebra.SesquilinearForm.TorsionFree

/-!
# Casimir detection of signed cluster relations

The Casimir kernel has order dividing the boundary saturation index.
For a squarefree boundary length the transported exchange-kernel basis alone
decides equality of signed loop pullbacks, including for two-component boundaries.

The comparison uses `exists_exchangeKernelAction_reflection_of_presentation`
to transport the signed Picard restriction to the exchange kernel.
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization (Point exists_exchangeKernelAction_reflection_of_presentation)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
  (href : Q.HasNodalModel c M)
  (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
  (hprim : IsPrimitive (Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal)))
  (hnef : (classOf(M.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M.surface ↘ S))
  (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(M.isEffectiveCartier_boundaryIdeal)
    classOf(M.isEffectiveCartier_boundaryIdeal) = 0)

local notation "D" => M.boundaryClass M.isEffectiveCartier_boundaryIdeal

include href hE hprim hnef hsq in
/-- The order of the signed Casimir kernel divides the saturation index of the marked
boundary lattice. -/
theorem card_ker_exchangeKernelAction_dvd_boundaryTorsion :
    Nat.card (exchangeKernelAction ℂ E).ker ∣
      Nat.card (AddCommGroup.torsion (L ⧸ Submodule.span ℤ (Set.range D))) := by
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  obtain ⟨Θ, e, -, hact, -⟩ :=
    exists_exchangeKernelAction_reflection_of_presentation
      Q P rfl rfl href M.isEffectiveCartier_boundaryIdeal hprim hnef hsq
  let : Scheme.IsRationalOver (M.surface ↘ S) := href.isRationalOver
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : LinearMap.IsPerfPair B := M.isPerfPair_of_isRationalOver
  let : Module.Finite ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.finite_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M.picardMarking.symm.surjective
  have hpair (x y : L) : B x y =
      Chow.classIntersectionNumber ℂ M.surface (M.picardMarking x).toMul
        (M.picardMarking y).toMul :=
    (M.intersectionBilinForm_picardMarking x y).symm.trans (Chow.intersectionBilinForm_apply ..)
  have hSymm : B.IsSymm := ⟨fun x y ↦
    (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hδ : IsPrimitive (∑ j, D j) :=
    M.picardMarking.isPrimitive_iff.mp (by rwa [M.picardMarking_sum_boundaryClass])
  rw [hact, MonoidHom.ker_comp_of_injective _ _
    ((LinearEquiv.autCongr e).injective.comp Subtype.val_injective),
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_comp_mulEquiv,
    Subgroup.card_map_of_injective Θ.symm.injective]
  exact card_ker_signedOrthogonalRestriction_dvd hSymm
    (M.intersectionForm_boundaryClass M.isEffectiveCartier_boundaryIdeal hnef hsq) hδ

include href hE hprim hnef hsq in
/-- If the marked boundary span is saturated, signed loop pullbacks agree exactly when
their transported integral basis columns agree, over any characteristic-zero field. -/
theorem xPullback_eq_iff_exponentEquiv_eq_on_basis_of_saturated_boundary
    (ht : Nat.card (AddCommGroup.torsion (L ⧸ Submodule.span ℤ (Set.range D))) = 1)
    (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {κ : Type*} (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker) :
    w.xPullback k = v.xPullback k ↔
      ∀ j, w.exponentEquiv (β j : Fin r → ℤ) = v.exponentEquiv (β j : Fin r → ℤ) := by
  have hd := Q.card_ker_exchangeKernelAction_dvd_boundaryTorsion href hE hprim hnef hsq
  rw [ht] at hd
  have hinj := (MonoidHom.ker_eq_bot_iff (exchangeKernelAction ℂ E)).mp
    ((Subgroup.eq_bot_iff_card _).mpr (Nat.dvd_one.mp hd))
  rw [Quiver.Path.xPullback_eq_iff_ySeed_coefficient_eq k w v,
    ← Quiver.Path.xPullback_eq_iff_ySeed_coefficient_eq ℂ w v]
  exact xPullback_eq_iff_exponentEquiv_eq_on_basis_of_injective ℂ E hinj w v β

include href hE hprim hnef hsq in
/-- For squarefree boundary length, Casimir basis columns alone decide signed relations. -/
theorem xPullback_eq_iff_exponentEquiv_eq_on_basis_of_squarefree
    (hn : Squarefree n) (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {κ : Type*} (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker) :
    w.xPullback k = v.xPullback k ↔
      ∀ j, w.exponentEquiv (β j : Fin r → ℤ) = v.exponentEquiv (β j : Fin r → ℤ) := by
  let : Scheme.IsRationalOver (M.surface ↘ S) := href.isRationalOver
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  have hp := M.isPerfPair_of_isRationalOver
  let : Module.IsTorsionFree ℤ L := hp.nondegenerate.1.isTorsionFree
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  have hδ : IsPrimitive (∑ j, D j) :=
    M.picardMarking.isPrimitive_iff.mp (by rwa [M.picardMarking_sum_boundaryClass])
  have hd := BoundaryCycle.natCard_torsion_quotient_sq_dvd
    (M.intersectionForm_boundaryClass M.isEffectiveCartier_boundaryIdeal hnef hsq) hδ
  have ht := Nat.isUnit_iff.mp (hn _ (by simpa only [pow_two] using hd))
  exact Q.xPullback_eq_iff_exponentEquiv_eq_on_basis_of_saturated_boundary
    href hE hprim hnef hsq ht k w v β

include href hE hprim hnef hsq in
/-- Decide signed loop equality at squarefree boundary length by comparing integer
columns of the transported exchange-kernel basis. -/
def decidableXPullbackEqOfSquarefreeBoundary
    (hn : Squarefree n) (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {κ : Type*} [Fintype κ] (β : Module.Basis κ ℤ E.matrix.mulVecLin.ker)
    (basisVectors : κ → Fin r → ℤ) (hb : basisVectors = fun j ↦ (β j : Fin r → ℤ)) :
    Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (∀ j, w.exponentEquiv (basisVectors j) = v.exponentEquiv (basisVectors j))
    (by
      rw [hb]
      exact (Q.xPullback_eq_iff_exponentEquiv_eq_on_basis_of_squarefree
        href hE hprim hnef hsq hn k w v β).symm)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
