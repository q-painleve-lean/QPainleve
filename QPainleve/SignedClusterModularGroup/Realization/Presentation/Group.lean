/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.NodalPicardGroupIdentification

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.PicardAction

/-!
# Picard group identifications from a marked reference fiber

The signed and unsigned cluster modular groups of a toric presentation are
identified by Picard pullback from one marked model of a primitive nef square-zero
anticanonical cycle. The family over the center torus comes from the reference
model. The unsigned equivalence is the restriction of the signed equivalence
to unsigned X maps and boundary rotations.

The construction uses `CompleteToricPresentation.exists_marked_family_of_nodal_model`
and `GeometricRealization.existsUnique_signedPicardEquiv_of_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

/-- The signed and unsigned opposite cluster modular groups of a complete toric
presentation of a primitive nef square-zero anticanonical cycle are the signed
boundary isometries and the boundary rotations. One marked nodal model supplies
the whole family, even when its reference center has repeated points.
`NodalPicardGroupIdentification` gives the Picard pullback and branch sign of
every compatible loop realization and the compatibility with the unsigned inclusions. -/
theorem exists_picardGroupEquivs_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M₀.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M₀.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(M₀.isEffectiveCartier_boundaryIdeal)
      classOf(M₀.isEffectiveCartier_boundaryIdeal) = 0) :
    ∃ P : NodalPicardGroupIdentification (B := B) Q ℂ E
        (M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal),
      P.family c = M₀ := by
  obtain ⟨M, hD, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model href M₀.isEffectiveCartier_boundaryIdeal
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  subst M₀
  let P := Fan.rayChargeSeed b Q.rays hE
  have hmark (z : Point Centers[r]) (j : ZMod n) :=
    congrFun (hfamily z).2 j
  obtain ⟨Θ, hΘ, -⟩ := existsUnique_signedPicardEquiv_of_presentation
    (Q := Q) (hD := hD) (hmark := hmark) P
    (Fan.rayChargeSeed_form _ _ _) (Fan.rayChargeSeed_charge _ _ _)
    (fun z _ ↦ (hfamily z).1) (hfamily c).1 hprim hnef hsq
  exact ⟨{ family := M
           hasNodalModel := fun z ↦ (hfamily z).1
           boundaryClass_eq := hmark
           signedEquiv := Θ
           sign_signedEquiv_apply_word := fun w ↦ by
             simpa only [SignedBoundaryIsometryGroup.sign_apply, MulEquiv.coe_toMonoidHom]
               using hΘ.sign_apply_word w
           signedEquiv_apply_word := hΘ.apply_of_realization
           sign_ker_unop := hΘ.sign_ker_unop }, rfl⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
