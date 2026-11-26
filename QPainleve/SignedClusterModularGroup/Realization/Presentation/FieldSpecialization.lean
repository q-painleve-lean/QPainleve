/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Specialization
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group

import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference
import QPainleve.SignedClusterModularGroup.SignExtension

/-!
# Field specialization for marked cluster modular groups

For a toric presentation of a primitive nef square-zero anticanonical cycle,
specializing the field of independent X coordinates preserves both cluster modular
groups. The integer invariants of a specialized loop are recovered from its X
pullback, and the marked relation criterion detects the same relations over both fields.
Consequently the Picard identifications over the complex numbers transport to
every coefficient field with their evaluation on loop representatives.

The comparison uses
`CompleteToricPresentation.IsSignedLoopComparisonInput.xPullback_eq_iff_xPullback_eq`.
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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local notation "cartier" => M₀.isEffectiveCartier_boundaryIdeal
local notation "δ" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf cartier))⁻¹

variable (k : Type*) [Field k]

private theorem injective_signedSpecialization
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    Function.Injective (signedClusterModularGroupSpecialization ℂ k E) := by
  intro g g' hg
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g'
  simp only [signedClusterModularGroupSpecialization_apply,
    signedClusterModularGroupMap_eq_iff] at hg ⊢
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, hp⟩ := href.exists_isNodalContraction cartier
  have hinput : Q.IsSignedLoopComparisonInput p E (p.numberedBoundaryOrders cartier) :=
    ⟨hE, rfl⟩
  exact (hinput.xPullback_eq_iff_xPullback_eq k ℂ hp hprim hnef hsq w.asHom v.asHom).mp hg

/-- Specialization identifies the signed point maps of a marked primitive nef square-zero
anticanonical cycle over the complex numbers with those over the target field. -/
noncomputable def signedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    SignedClusterModularGroup ℂ E ≃* SignedClusterModularGroup k E :=
  MulEquiv.ofBijective (signedClusterModularGroupSpecialization ℂ k E)
    ⟨injective_signedSpecialization Q k href hE hprim hnef hsq,
      signedClusterModularGroupSpecialization_surjective ℂ k E⟩

/-- The signed equivalence acts by evaluating signed loops over the target field. -/
@[simp]
theorem coe_signedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    ⇑(Q.signedSpecializationEquiv k href hE hprim hnef hsq) =
      signedClusterModularGroupSpecialization ℂ k E := (rfl)

/-- Specialization identifies the unsigned point maps of a marked primitive nef square-zero
anticanonical cycle over the complex numbers with those over the target field. -/
noncomputable def unsignedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    ClusterModularGroup ℂ E ≃* ClusterModularGroup k E :=
  MulEquiv.ofBijective (clusterModularGroupSpecialization ℂ k E)
    ⟨clusterModularGroupSpecialization_injective_of_signed ℂ k E
      (injective_signedSpecialization Q k href hE hprim hnef hsq),
      clusterModularGroupSpecialization_surjective ℂ k E⟩

/-- The unsigned equivalence acts by evaluating inversion-free loops over the target field. -/
@[simp]
theorem coe_unsignedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    ⇑(Q.unsignedSpecializationEquiv k href hE hprim hnef hsq) =
      clusterModularGroupSpecialization ℂ k E := (rfl)

/-- The Picard identifications of the opposite signed and unsigned cluster
modular groups hold over every field of X coefficients. They retain the
ordered branch sign and compute the complex geometric Picard pullback of
each loop. The unsigned inclusion corresponds to the boundary rotations. -/
theorem exists_picardGroupEquivs_over_field_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef ℂ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ δ = 0) :
    ∃ P : NodalPicardGroupIdentification (B := B) Q k E (M₀.boundaryClass cartier),
      P.family c = M₀ := by
  obtain ⟨P, hP⟩ := Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  let e := Q.signedSpecializationEquiv k href hE hprim hnef hsq
  have hword (w : Word E E) :
      (MulEquiv.op e).symm (op (signedClusterModularGroupMap k E (End.of w))) =
        op (signedClusterModularGroupMap ℂ E (End.of w)) :=
    (MulEquiv.op e).symm_apply_eq.mpr (by simp [e])
  let Θ := (MulEquiv.op e).symm.trans P.signedEquiv
  have hsign (w : Word E E) :
      (Θ (op (signedClusterModularGroupMap k E (End.of w)))).val.2 =
        (-1 : ℤˣ) ^ w.inversionCount := by
    simpa only [Θ, MulEquiv.trans_apply, hword] using P.sign_signedEquiv_apply_word w
  exact ⟨{ family := P.family
           hasNodalModel := P.hasNodalModel
           boundaryClass_eq := P.boundaryClass_eq
           signedEquiv := Θ
           sign_signedEquiv_apply_word := hsign
           signedEquiv_apply_word := fun w {_} _ _ R hR ↦ by
             simpa only [Θ, MulEquiv.trans_apply, hword] using P.signedEquiv_apply_word w R hR
           sign_ker_unop := sign_ker_unop_eq_range_of_apply_word Θ.toMonoidHom
             (fun w ↦ (sign_apply B _ _).trans (hsign w))
             (href.exchangeMatrix_ne_zero hE hprim hnef hsq) }, hP⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
