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
# Picard isometries of a boundary with at least three components

When the marked boundary components are distinguished by their classes and the cycle
has length at least three, the Picard pullback determines the dihedral boundary action.
In this case the signed cluster modular group is anti-isomorphic to the subgroup
of Picard isometries acting by rotations or reflections of the numbered boundary.
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

local instance instDihedralNonemptyCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instDihedralNeZeroLength : NeZero Q.length := Q.neZero
local instance instDihedralPrestableBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Models[" M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun z : Point Centers[r] ↦ χ[z]) C

/-- For a complete toric presentation of a primitive nef square-zero anticanonical cycle
with at least three components, Picard pullback identifies the opposite signed cluster
modular group with the underlying Picard isometries acting by boundary rotations or
reflections. A marked nodal model supplies the family over the center torus. For any
loop, the unique forward dihedral action whose inverse is induced on the boundary
classes has sign given by the parity of the inversions. -/
theorem exists_picardIsometryEquiv_of_nodal_model
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M₀.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M₀.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(M₀.isEffectiveCartier_boundaryIdeal)
      classOf(M₀.isEffectiveCartier_boundaryIdeal) = 0)
    (hn : 3 ≤ n) :
    let d := M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal
    ∃ (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
      (hD : ∀ z, D[M z].IsEffectiveCartier)
      (hmark : ∀ z j, (M z).boundaryClass (hD z) j = d j)
      (Ψ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* (toIsometry B d).range),
      M c = M₀ ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      ∀ w : Word E E,
        let x := op (signedClusterModularGroupMap ℂ E (End.of w))
        (∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[M,C] → (Ψ x).val = toIsometry B d (R.toSignedBoundaryIsometry d hD hmark)) ∧
        ∃ a : DihedralGroup n, DihedralGroup.cycleOrientationSign a =
          (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ a' : DihedralGroup n,
            (∀ j, (Ψ x).val.val (d (DihedralGroup.cycleVertexPerm a' j)) = d j) ↔ a' = a := by
  obtain ⟨M, hD, hM, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model href M₀.isEffectiveCartier_boundaryIdeal
  dsimp only
  subst M₀
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  have hmark (z : Point Centers[r]) (j : ZMod n) := congrFun (hfamily z).2 j
  obtain ⟨Θ, ⟨hΘ, -⟩, -⟩ := existsUnique_signedPicardEquiv_of_presentation
    (Q := Q) (hD := hD) (hmark := hmark) P rfl rfl (fun z _ ↦ (hfamily z).1)
    (hfamily c).1 hprim hnef hsq
  have hd := (M c).boundaryClass_injective_of_nef_square_zero _ hnef hsq
  refine ⟨M, hD, hmark, Θ.trans (MonoidHom.ofInjective (toIsometry_injective B _ hn hd)), rfl,
    fun z ↦ (hfamily z).1, fun w ↦ ?_⟩
  simp only [MulEquiv.trans_apply, MonoidHom.ofInjective_apply]
  refine ⟨fun R hR ↦ congrArg (toIsometry B _) ((hΘ w).2 R hR), ?_⟩
  let g := Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))
  obtain ⟨a, ha, hpb⟩ := exists_cycleAction_pullback B _ g
  refine ⟨a, ha.trans (hΘ w).1, fun a' ↦ ⟨fun hpb' ↦ ?_, fun h ↦ h ▸ hpb⟩⟩
  apply DihedralGroup.cycleVertexPerm_injective hn
  ext j
  exact hd ((toIsometry B _ g).val.injective ((hpb' j).trans (hpb j).symm))

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
