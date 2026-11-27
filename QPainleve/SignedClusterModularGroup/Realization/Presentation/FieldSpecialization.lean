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
Consequently the Picard identifications over the geometric coefficient field transport to
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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀] [Uncountable k₀] [CharZero k₀]

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation k₀ i b r L γ)
  {c : Point (Over.mk (QPainleve.CharacterTorus.structureMap k₀ (Fin r →
    ℤ)))} {M₀ : MarkedSurface k₀ n B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}

local notation "cartier" => M₀.isEffectiveCartier_boundaryIdeal
local notation "δ" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf cartier))⁻¹

variable (K k : Type*) [Field K] [CharZero K] [Field k]

private theorem injective_signedSpecialization
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    Function.Injective (signedClusterModularGroupSpecialization K k E) := by
  intro g g' hg
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective K E g
  obtain ⟨v, rfl⟩ := signedClusterModularGroupMap_surjective K E g'
  simp only [signedClusterModularGroupSpecialization_apply,
    signedClusterModularGroupMap_eq_iff] at hg ⊢
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, hp⟩ := href.exists_isNodalContraction cartier
  have hinput : Q.IsSignedLoopComparisonInput p E (p.numberedBoundaryOrders cartier) :=
    ⟨hE, rfl⟩
  exact (hinput.xPullback_eq_iff_xPullback_eq k K hp hprim hnef hsq w.asHom v.asHom).mp hg

/-- Specialization identifies the signed point maps of a marked primitive nef square-zero
anticanonical cycle over a characteristic-zero field with those over the target field. -/
noncomputable def signedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    SignedClusterModularGroup K E ≃* SignedClusterModularGroup k E :=
  MulEquiv.ofBijective (signedClusterModularGroupSpecialization K k E)
    ⟨injective_signedSpecialization Q K k href hE hprim hnef hsq,
      signedClusterModularGroupSpecialization_surjective K k E⟩

/-- The signed equivalence acts by evaluating signed loops over the target field. -/
@[simp]
theorem coe_signedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    ⇑(Q.signedSpecializationEquiv K k href hE hprim hnef hsq) =
      signedClusterModularGroupSpecialization K k E := (rfl)

/-- Specialization identifies the unsigned point maps of a marked primitive nef square-zero
anticanonical cycle over a characteristic-zero field with those over the target field. -/
noncomputable def unsignedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    ClusterModularGroup K E ≃* ClusterModularGroup k E :=
  MulEquiv.ofBijective (clusterModularGroupSpecialization K k E)
    ⟨clusterModularGroupSpecialization_injective_of_signed K k E
      (injective_signedSpecialization Q K k href hE hprim hnef hsq),
      clusterModularGroupSpecialization_surjective K k E⟩

/-- The unsigned equivalence acts by evaluating inversion-free loops over the target field. -/
@[simp]
theorem coe_unsignedSpecializationEquiv
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    ⇑(Q.unsignedSpecializationEquiv K k href hE hprim hnef hsq) =
      clusterModularGroupSpecialization K k E := (rfl)

/-- The Picard identifications of the opposite signed and unsigned cluster
modular groups hold over every field of X coefficients. They retain the
ordered branch sign and compute the geometric Picard pullback of
each loop. The unsigned inclusion corresponds to the boundary rotations. -/
theorem exists_picardGroupEquivs_over_field_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ))
    (hnef : LineBundleClass.IsNef k₀ (M₀.surface ↘ S) δ)
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface δ δ = 0) :
    ∃ P : NodalPicardGroupIdentification (B := B) Q k E (M₀.boundaryClass cartier),
      P.family c = M₀ := by
  obtain ⟨P, hP⟩ := Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  let e := Q.signedSpecializationEquiv k₀ k href hE hprim hnef hsq
  have hword (w : Word E E) :
      (MulEquiv.op e).symm (op (signedClusterModularGroupMap k E (End.of w))) =
        op (signedClusterModularGroupMap k₀ E (End.of w)) :=
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
