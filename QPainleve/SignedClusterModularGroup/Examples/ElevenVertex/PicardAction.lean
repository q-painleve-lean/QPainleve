/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Relations
public import QPainleve.SignedClusterModularGroup.Realization.Relations.PicardAction

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# The eleven-vertex word under Picard pullback

For a marked nodal contraction of the eleven-vertex seed, the exchange-kernel
transport identifies the inversion–mutation–transposition word with the pure
sign change. The word negates the exchange kernel, and the marked Casimir
comparison identifies this action with signed Picard restriction.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open QPainleve.SignedClusterModularGroup QPainleve.SignedClusterModularGroup.GeometricRealization
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.ElevenVertex

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "B" => exchangeMatrix
local notation "Γ" => SignedClusterModularGroup k₀ B
local notation "eval[" w "]" => op (signedClusterModularGroupMap k₀ B (End.of w))

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers" => Over.mk (structureMap k₀ (Fin 11 → ℤ))
local notation "XTor" => scheme k₀ (Fin 11 →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {Q : CompleteToricPresentation k₀ i b 11 L γ}
  {c₀ : Point (Over.mk (structureMap k₀ (Fin 11 → ℤ)))}
  {M₀ : MarkedSurface k₀ 1 H (scheme k₀ (Fin 11 →₀ ℤ))}

local instance (Q : CompleteToricPresentation k₀ i b 11 L γ) : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance (Q : CompleteToricPresentation k₀ i b 11 L γ) : NeZero Q.length := Q.neZero
local instance (Q : CompleteToricPresentation k₀ i b 11 L γ) :
    PrestableFamily ((Q.fan.toricBoundaryIdeal k₀ Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "classes[" M "]" => MarkedSurface.boundaryClass M cartier[M]

/-- The signed Picard equivalence in a marked one-component model of the
eleven-vertex seed, with its geometric loop formulas and central sign involution. -/
@[ext]
structure InvolutionPicardIdentification (Q : CompleteToricPresentation k₀ i b 11 L γ)
    (c₀ : Point Centers) (M₀ : MarkedSurface k₀ 1 H XTor) where
  /-- The marked surfaces over the center torus. -/
  family : Point Centers → MarkedSurface k₀ 1 H XTor
  /-- The family contains the specified marked surface at the reference center. -/
  family_center : family c₀ = M₀
  /-- Each fiber has a nodal model in the same toric presentation. -/
  hasNodalModel (c : Point Centers) : Q.HasNodalModel c (family c)
  /-- The marked boundary classes are constant in the family. -/
  boundaryClass_eq (c : Point Centers) (j : ZMod 1) : classes[family c] j = classes[M₀] j
  /-- The signed group in pullback order identifies with the signed boundary isometries. -/
  signedEquiv : Γᵐᵒᵖ ≃* signedBoundaryIsometryGroup H classes[M₀]
  /-- The inversion–mutation–transposition word is the pure sign change. -/
  signedEquiv_apply_involutionWord :
    signedEquiv eval[involutionWord] = centralSign H classes[M₀] (by decide)
  /-- The Picard sign on a loop is its inversion parity. -/
  sign_signedEquiv_apply_word (w : Word B B) :
    (signedEquiv eval[w]).val.2 = (-1 : ℤˣ) ^ w.inversionCount
  /-- Each geometric realization of a loop gives its Picard pullback and branch sign. -/
  signedEquiv_apply_of_realization (w : Word B B)
      {C : (Centers).left.PartialMap (Centers).left} [IsDominant C.hom]
      [C.IsOver (Centers).hom (Centers).hom]
      (R : GeometricRealization family family C (w.xRationalMap k₀)) :
    signedEquiv eval[w] =
      R.toSignedBoundaryIsometry classes[M₀] (fun c ↦ cartier[family c]) boundaryClass_eq

attribute [simp] InvolutionPicardIdentification.family_center
  InvolutionPicardIdentification.boundaryClass_eq
  InvolutionPicardIdentification.signedEquiv_apply_involutionWord
  InvolutionPicardIdentification.sign_signedEquiv_apply_word

/-- A marked nodal contraction of the eleven-vertex seed with primitive nef square-zero
boundary gives the signed Picard equivalence carrying the specified word to the pure sign
change. -/
theorem nonempty_involutionPicardIdentification_of_nodal_contraction
    [Uncountable k₀] [NeZero (2 : k₀)]
    (p₀ : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c₀] M₀)
    (hnodal₀ : p₀.IsNodalContraction)
    (hE : (B).matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef k₀ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    Nonempty (InvolutionPicardIdentification Q c₀ M₀) := by
  obtain ⟨A⟩ := Q.nonempty_signedLoopPicardComparison_of_nodal_contraction
    p₀ hnodal₀ hE hprim hnef hsq
  let G := A.identification
  let : IsRationalOver (M₀.surface ↘ S) := (Q.hasNodalModel_of_contraction hnodal₀).isRationalOver
  let : M₀.surface.IsProjectiveOver k₀ := M₀.projective
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : Module.Free ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.free_picard_of_isRationalOver k₀
  let : Module.Finite ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.finite_picard_of_isRationalOver k₀
  let : Module.Free ℤ L := Module.Free.of_equiv M₀.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M₀.picardMarking.symm.surjective
  have hpair (x y : L) : H x y = Chow.classIntersectionNumber k₀ M₀.surface
      (M₀.picardMarking x).toMul (M₀.picardMarking y).toMul :=
    (M₀.intersectionBilinForm_picardMarking x y).symm.trans (Chow.intersectionBilinForm_apply ..)
  have hSymm : H.IsSymm :=
    ⟨fun x y ↦ (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hsign := (SignedBoundaryIsometryGroup.sign_apply H classes[M₀] _).trans
    (G.sign_signedEquiv_apply_word involutionWord)
  rw [inversionCount_involutionWord, pow_one] at hsign
  have hneg (x : H.orthogonal (Submodule.span ℤ (Set.range classes[M₀]))) :
      (signedOrthogonalRestriction H classes[M₀] (G.signedEquiv eval[involutionWord])).val x =
        -x := by
    let e := A.casimir.exchangeKernelEquiv
    have hact := A.casimir.exchangeKernelEquiv_eq_autCongr involutionWord
    rw [A.casimir_picardEquiv] at hact
    apply e.injective
    simpa only [e, LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, map_neg,
      involutionWord_exchangeKernelEquiv_apply] using DFunLike.congr_fun hact.symm (e x)
  have hz := eq_centralSign_of_signedOrthogonalRestriction hSymm
    M₀.isPerfPair_of_isRationalOver.nondegenerate (M₀.intersectionForm_boundaryClass _ hnef hsq)
    _ hsign hneg
  exact ⟨⟨G.family, A.family_center, G.hasNodalModel, G.boundaryClass_eq, G.signedEquiv, hz,
    G.sign_signedEquiv_apply_word, fun w {C} _ _ R ↦
      G.signedEquiv_apply_word w R
        (fun a ↦ (G.hasNodalModel (a ≫ C.domainTarget)).nonempty_contractedToricFiber)⟩⟩

end QPainleve.ElevenVertex
