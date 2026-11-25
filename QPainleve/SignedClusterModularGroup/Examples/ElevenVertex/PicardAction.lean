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

For a marked nodal contraction of the eleven-vertex seed, the integer
invariants identify the inversion–mutation–transposition word with the pure
sign change. The sign-adjusted restriction of this element negates the
Casimir basis, and the single boundary component forces the forward label.
The comparison uses `exists_picardEquiv_signedLoopInvariants_of_nodal_contraction`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open QPainleve.SignedClusterModularGroup QPainleve.SignedClusterModularGroup.GeometricRealization
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.ElevenVertex

local notation "B" => exchangeMatrix
local notation "K" => exchangeMatrix.matrix.mulVecLin.ker
local notation "Γ" => SignedClusterModularGroup ℂ B
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ B (End.of w))

private theorem signedOrthogonalRestriction_eq_neg_of_involution_invariants
    {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {d : ZMod 1 → L}
    (e : H.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K)
    (g : signedBoundaryIsometryGroup H d) (orders : Fin 1 → Fin 11 → ℤ) {j : Fin 1}
    (h : involutionWord.signedLoopInvariants (fun j ↦ (exchangeKernelBasis j : Fin 11 → ℤ))
        orders (orders 0) =
      ⟨sign H d g, Matrix.of (fun i j ↦
        ((LinearEquiv.autCongr e (signedOrthogonalRestriction H d g).val)
          (exchangeKernelBasis j) : Fin 11 → ℤ) i), some j⟩)
    (x : H.orthogonal (Submodule.span ℤ (Set.range d))) :
    (signedOrthogonalRestriction H d g).val x = -x := by
  -- The exponent columns do not depend on the table used for the boundary search.
  have hcols := congrArg SignedLoopInvariants.kernelColumns h
  rw [Path.signedLoopInvariants_kernelColumns] at hcols
  have hact : LinearEquiv.autCongr e (signedOrthogonalRestriction H d g).val =
      involutionWord.exchangeKernelEquiv := by
    apply LinearEquiv.toLinearMap_injective
    apply exchangeKernelBasis.ext
    intro j
    apply Subtype.ext
    funext i
    simpa only [LinearEquiv.coe_coe, Matrix.of_apply, coe_exchangeKernelBasis_apply,
      Path.coe_exchangeKernelEquiv_apply] using
      congrArg (fun m : Matrix (Fin 11) (Fin 9) ℤ ↦ m i j) hcols.symm
  apply e.injective
  simpa only [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply, map_neg,
    involutionWord_exchangeKernelEquiv_apply] using DFunLike.congr_fun hact (e x)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers" => Over.mk (structureMap ℂ (Fin 11 → ℤ))
local notation "XTor" => scheme ℂ (Fin 11 →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {Q : CompleteToricPresentation i b 11 L γ}
  {c₀ : Point Centers} {M₀ : MarkedSurface ℂ 1 H XTor}

local instance (Q : CompleteToricPresentation i b 11 L γ) : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance (Q : CompleteToricPresentation i b 11 L γ) : NeZero Q.length := Q.neZero
local instance (Q : CompleteToricPresentation i b 11 L γ) :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "classes[" M "]" => MarkedSurface.boundaryClass M cartier[M]

/-- The signed Picard equivalence in a marked one-component model of the
eleven-vertex seed, with its geometric loop formulas and central sign involution. -/
@[ext]
structure InvolutionPicardIdentification (Q : CompleteToricPresentation i b 11 L γ)
    (c₀ : Point Centers) (M₀ : MarkedSurface ℂ 1 H XTor) where
  /-- The marked surfaces over the center torus. -/
  family : Point Centers → MarkedSurface ℂ 1 H XTor
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
      (R : GeometricRealization family family C (w.xRationalMap ℂ)) :
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
    (p₀ : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c₀] M₀)
    (hnodal₀ : p₀.IsNodalContraction)
    (hE : (B).matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    Nonempty (InvolutionPicardIdentification Q c₀ M₀) := by
  obtain ⟨M, _, hmark, Θ, e, hMc, hM, hΘ, _, _, hInv⟩ :=
    Q.exists_picardEquiv_signedLoopInvariants_of_nodal_contraction p₀ hnodal₀ hE hprim hnef hsq
  let : IsRationalOver (M₀.surface ↘ S) := (Q.hasNodalModel_of_contraction hnodal₀).isRationalOver
  let : M₀.surface.IsProjectiveOver ℂ := M₀.projective
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : Module.Free ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass M₀.surface)) :=
    M₀.surface.finite_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv M₀.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M₀.picardMarking.symm.surjective
  have hpair (x y : L) : H x y = Chow.classIntersectionNumber ℂ M₀.surface
      (M₀.picardMarking x).toMul (M₀.picardMarking y).toMul :=
    (M₀.intersectionBilinForm_picardMarking x y).symm.trans (Chow.intersectionBilinForm_apply ..)
  have hSymm : H.IsSymm :=
    ⟨fun x y ↦ (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  obtain ⟨_, hcomp, _⟩ := hInv involutionWord exchangeKernelBasis
  have hsign := (hΘ involutionWord).1
  rw [inversionCount_involutionWord, pow_one] at hsign
  have hz := eq_centralSign_of_signedOrthogonalRestriction hSymm
    M₀.isPerfPair_of_isRationalOver.nondegenerate (M₀.intersectionForm_boundaryClass _ hnef hsq)
    _ hsign (signedOrthogonalRestriction_eq_neg_of_involution_invariants e _ _ hcomp)
  refine ⟨⟨M, hMc, hM, hmark, Θ, hz, ?_, fun w {C} _ _ R ↦ ?_⟩⟩
  · intro w
    simpa only [SignedBoundaryIsometryGroup.sign_apply] using (hΘ w).1
  · exact (hΘ w).2 R (fun a ↦ (hM (a ≫ C.domainTarget)).nonempty_contractedToricFiber)

/-- In a marked nodal contraction of the eleven-vertex seed with a primitive nef
square-zero boundary of one component, the full signed Picard equivalence sends the
inversion–mutation–transposition word to the pure sign change. The marked family
contains the specified marked surface at its reference center. The same equivalence
gives geometric Picard pullback and the inversion sign for signed loops. -/
theorem exists_picardEquiv_apply_involutionWord_of_nodal_contraction
    (Q : CompleteToricPresentation i b 11 L γ)
    (p₀ : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c₀] M₀)
    (hnodal₀ : p₀.IsNodalContraction)
    (hE : (B).matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    let d := M₀.boundaryClass cartier[M₀]
    ∃ (M : Point Centers → MarkedSurface ℂ 1 H XTor)
      (hD : ∀ c, D[M c].IsEffectiveCartier)
      (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
      (Θ : Γᵐᵒᵖ ≃* signedBoundaryIsometryGroup H d),
      M c₀ = M₀ ∧ (∀ c, Q.HasNodalModel c (M c)) ∧
      Θ eval[involutionWord] = centralSign H d (by decide) ∧
      ∀ w : Word B B,
        sign H d (Θ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : (Centers).left.PartialMap (Centers).left} [IsDominant C.hom]
            [C.IsOver (Centers).hom (Centers).hom]
            (R : GeometricRealization M M C (w.xRationalMap ℂ)),
            Θ eval[w] = R.toSignedBoundaryIsometry d hD hmark := by
  obtain ⟨I⟩ := nonempty_involutionPicardIdentification_of_nodal_contraction p₀ hnodal₀ hE
    hprim hnef hsq
  refine ⟨I.family, (fun c ↦ cartier[I.family c]), I.boundaryClass_eq, I.signedEquiv,
    I.family_center, I.hasNodalModel, I.signedEquiv_apply_involutionWord,
    fun w ↦ ⟨?_, fun R ↦ I.signedEquiv_apply_of_realization w R⟩⟩
  simpa only [SignedBoundaryIsometryGroup.sign_apply] using I.sign_signedEquiv_apply_word w

end QPainleve.ElevenVertex
