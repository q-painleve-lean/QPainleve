/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

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

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

/-- The signed and unsigned opposite cluster modular groups of a complete toric
presentation of a primitive nef square-zero anticanonical cycle are the signed
boundary isometries and the boundary rotations. One marked nodal model supplies
the whole family, even when its reference center has repeated points. The signed
equivalence computes the Picard pullback of every compatible loop realization and
retains the branch sign. The two equivalences commute with the unsigned inclusions. -/
theorem exists_picardGroupEquivs_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M₀.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M₀.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(M₀.isEffectiveCartier_boundaryIdeal)
      classOf(M₀.isEffectiveCartier_boundaryIdeal) = 0) :
    let d := M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hD : ∀ z, D[M z].IsEffectiveCartier)
      (hmark : ∀ z j, (M z).boundaryClass (hD z) j = d j)
      (Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
      (Θrot : (ClusterModularGroup ℂ E)ᵐᵒᵖ ≃* boundaryRotationGroup B d),
      M c = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      (∀ (w : Word E E),
        sign B d (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))) =
          (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[M,C] →
          Θ (op (signedClusterModularGroupMap ℂ E (End.of w))) =
            R.toSignedBoundaryIsometry d hD hmark) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      (∀ x, rotationInclusion B d (Θrot x) =
        Θ (MonoidHom.op (clusterModularGroupInclusion ℂ E) x)) := by
  obtain ⟨M, hD, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model href M₀.isEffectiveCartier_boundaryIdeal
  dsimp only
  subst M₀
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  have hmark (z : Point Centers[r]) (j : ZMod n) :=
    congrFun (hfamily z).2 j
  obtain ⟨Θ, ⟨hΘ, hsign⟩, -⟩ := existsUnique_signedPicardEquiv_of_presentation
    (Q := Q) (hD := hD) (hmark := hmark) P rfl rfl (fun z _ ↦ (hfamily z).1)
    (hfamily c).1 hprim hnef hsq
  let ρ := picardRotationHom Θ.toMonoidHom hsign.ge
  have hinj : Function.Injective ρ := by
    intro x y hxy
    have h := congrArg (rotationInclusion B _) hxy
    simp only [ρ, rotationInclusion_picardRotationHom_apply, MulEquiv.coe_toMonoidHom] at h
    exact unop_injective
      (clusterModularGroupInclusion_injective ℂ E (op_injective (Θ.injective h)))
  have hsurj : Function.Surjective ρ :=
    (picardRotationHom_surjective_iff Θ.toMonoidHom hsign).mpr
      (fun g _ ↦ MonoidHom.mem_range.mpr (Θ.surjective g))
  exact ⟨M, hD, hmark, Θ, MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩, rfl,
    fun z ↦ (hfamily z).1, hΘ, hsign, rotationInclusion_picardRotationHom_apply _ _⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
