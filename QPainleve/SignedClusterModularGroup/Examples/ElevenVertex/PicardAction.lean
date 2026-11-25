/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Relations
public import QPainleve.SignedClusterModularGroup.Realization.Relations.PicardAction

import QPainleve.SignedClusterModularGroup.Realization.Relations.OneComponent

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

private theorem eq_centralSign_of_involution_invariants
    {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {d : ZMod 1 → L}
    (hinj : Function.Injective (signedOrthogonalRestriction H d))
    (e : H.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] K)
    (g : signedBoundaryIsometryGroup H d) (orders : Fin 1 → Fin 11 → ℤ)
    (h : involutionWord.signedLoopInvariants (fun j ↦ (exchangeKernelBasis j : Fin 11 → ℤ))
        orders (orders 0) =
      (sign H d g, Matrix.of (fun i j ↦
        ((LinearEquiv.autCongr e (signedOrthogonalRestriction H d g).val)
          (exchangeKernelBasis j) : Fin 11 → ℤ) i), some 0)) :
    g = centralSign H d (by decide) := by
  -- The exponent columns do not depend on the table used for the boundary search.
  let cols (v : ℤˣ × Matrix (Fin 11) (Fin 9) ℤ × Option (Fin 1)) := v.2.1
  have hcols := congrArg cols h
  have hneg := congrArg cols involutionWord_signedLoopInvariants
  simp only [cols, Path.signedLoopInvariants_def, coe_exchangeKernelBasis_apply] at hcols hneg
  have hmatrix := hcols.symm.trans hneg
  apply hinj
  apply Subtype.val_injective
  apply (LinearEquiv.autCongr e).injective
  apply LinearEquiv.toLinearMap_injective
  apply exchangeKernelBasis.ext
  intro j
  apply Subtype.ext
  funext i
  simpa only [LinearEquiv.coe_coe, LinearEquiv.autCongr_apply_apply,
    signedOrthogonalRestriction_centralSign_apply, map_neg, LinearEquiv.apply_symm_apply,
    Matrix.of_apply, Matrix.neg_apply, Submodule.coe_neg, Pi.neg_apply,
    coe_exchangeKernelBasis_apply] using
    congrArg (fun m : Matrix (Fin 11) (Fin 9) ℤ ↦ m i j) hmatrix

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
  (Q : CompleteToricPresentation i b 11 L γ)
  {c₀ : Point Centers} {M₀ : MarkedSurface ℂ 1 H XTor}

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

/-- In a marked nodal contraction of the eleven-vertex seed with a primitive nef
square-zero boundary of one component, the full signed Picard equivalence sends the
inversion–mutation–transposition word to the pure sign change. The marked family
contains the specified marked surface at its reference center. The same equivalence
gives geometric Picard pullback and the inversion sign for signed loops. -/
theorem exists_picardEquiv_apply_involutionWord_of_nodal_contraction
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
  dsimp only
  obtain ⟨M, hD, hmark, Θ, e, hMc, hM, hΘ, _, _, hInv⟩ :=
    Q.exists_picardEquiv_signedLoopInvariants_of_nodal_contraction p₀ hnodal₀ hE hprim hnef hsq
  obtain ⟨Θ₀, _, _, hact, hfaithful, _⟩ :=
    Q.exists_picardEquiv_with_faithful_exchangeKernelAction
      (Q.hasNodalModel_of_contraction hnodal₀) hE hprim hnef hsq
  have hinj : Function.Injective (signedOrthogonalRestriction H (M₀.boundaryClass cartier[M₀])) :=
    fun g g' hh ↦ Θ₀.symm.injective (hfaithful (by
      simp only [hact, MulEquiv.apply_symm_apply, hh]))
  obtain ⟨j, hcomp, _⟩ := hInv involutionWord exchangeKernelBasis
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  refine ⟨M, hD, hmark, Θ, hMc, hM, eq_centralSign_of_involution_invariants hinj e _ _ hcomp,
    fun w ↦ ⟨(hΘ w).1, ?_⟩⟩
  intro C _ _ R
  exact (hΘ w).2 R (fun a ↦ by
    obtain ⟨q, _⟩ := (Q.hasNodalModel_iff _ _).mp (hM (a ≫ C.domainTarget))
    exact ⟨q⟩)

end QPainleve.ElevenVertex
