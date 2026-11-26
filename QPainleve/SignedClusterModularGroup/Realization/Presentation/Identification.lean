/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Presentation.PicardGroupIdentification
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Boundary.Conjugation
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group

/-!
# Cluster modular groups of numbered surface presentations

Specified nodal and internal blowup towers determine the seed and the Picard
group identifications of the original numbered surface. A finite integral
marking supplies the moving family, and conjugation by that marking recovers
the group on the actual Picard lattice. The oriented toric basis is chosen by
`exists_marked_reference_fiber_of_ordered_towers`, and the identifications are
given by `CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {n r : ℕ} [NeZero n]

local instance : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => (Fin (Module.finrank ℤ Pic) → ℤ)
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

/-- For a specified ordered toric presentation of a primitive nef square-zero
anticanonical cycle, the signed and unsigned opposite cluster modular groups
identify with the signed boundary isometries and rotations of the original
Picard group. The reference family keeps the original surface and numbering.
The oriented frame retains the input fan and all ray labels, and in the
transposed frame the reference center parameters are inverted. The signed
equivalence evaluates by geometric Picard pullback and the branch sign. -/
theorem exists_picardGroupEquivs_of_toric_presentation
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    ∃ Q : PicardGroupIdentification i r A hD,
      ((Q.basis = b ∧ parameters[Q.center] = P.parameters) ∨
        (Q.basis = b.reindex (Equiv.swap 0 1) ∧ parameters[Q.center] = P.parameters⁻¹)) ∧
      (∃ hfan : Q.presentation.fan = P.fan, hfan ▸ Q.presentation.rays = P.rays) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  let a : L ≃ₗ[ℤ] Pic := (Module.finBasis ℤ Pic).equivFun.symm
  let H := (B).comp a.toLinearMap a.toLinearMap
  let μ : H.IsometryEquiv B := ((B).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', R, hframe, hrays⟩ :=
    exists_marked_reference_fiber_of_ordered_towers P.regular P.complete P.rays P.parameters
      P.isNodal P.iso P.iso_over P.iso_boundary hD A μ
  let Q := R.presentation
  let M₀ := MarkedSurface.ofBoundary D A μ R.evaluation
  have hδ : δ[M₀.isEffectiveCartier_boundaryIdeal] = δ[hD] :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (MarkedSurface.ofBoundary_ker D A μ R.evaluation))
  let m := chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays)
  let skew :=
    isSkewSymmetrizer_chargeExchangeMatrix _ b'.detDualEquiv_self (Fan.rayChargeMap Q.rays)
  let E := SkewExchangeMatrix.ofMatrix m skew
  have hE : E.matrix = m := SkewExchangeMatrix.matrix_ofMatrix _ _
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let d := classes[A,hD]
  have hd : M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal = μ.symm ∘ d :=
    funext (MarkedSurface.boundaryClass_ofBoundary D A μ R.evaluation hD)
  have hgroups := Q.exists_picardGroupEquivs_of_nodal_model (M₀ := M₀) R.hasNodalModel hE
    (by rwa [hδ]) (by rwa [hδ]) (by rwa [hδ])
  rw [hd] at hgroups
  obtain ⟨identification, hM⟩ := hgroups
  let Θ := identification.signedEquiv
  have hmatch (j : ZMod n) : μ.symm (d j) = (μ.symm ∘ d) ((1 : ℤˣ) • j + 0) := by simp
  let α := SignedBoundaryIsometryGroup.congr μ.symm hmatch
  let β := boundaryRotationGroupCongr μ.symm hmatch
  have hcomp : (sign B d).comp (Θ.trans α).toMonoidHom =
      (sign H (μ.symm ∘ d)).comp Θ.toMonoidHom :=
    MonoidHom.ext fun x ↦ by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        α, SignedBoundaryIsometryGroup.sign_apply, coe_congr]
  refine ⟨{ form := H, marking := μ, basis := b', presentation := Q
            center := R.center, evaluation := R.evaluation, exchangeMatrix := E
            family := identification.family
            signedEquiv := Θ.trans α, unsignedEquiv := identification.unsignedEquiv.trans β
            matrix_eq := hE
            family_center := hM, hasNodalModel := identification.hasNodalModel
            boundaryClass_eq := identification.boundaryClass_eq
            sign_signedEquiv_apply_word := fun w ↦ by
              simpa only [MonoidHom.comp_apply, SignedBoundaryIsometryGroup.sign_apply,
                MulEquiv.coe_toMonoidHom] using
                (DFunLike.congr_fun hcomp _).trans
                  ((SignedBoundaryIsometryGroup.sign_apply H _ _).trans
                    (identification.sign_signedEquiv_apply_word w))
            signedEquiv_apply_word := ?_, sign_ker_unop := ?_
            rotationInclusion_unsignedEquiv_apply := ?_ }, hframe, hrays⟩
  · intro w C _ _ R hR
    simp only [MulEquiv.trans_apply, α, Θ, coe_congr, identification.signedEquiv_apply_word w R hR,
      coe_toSignedBoundaryIsometry]
    rfl
  · rw [hcomp, identification.sign_ker_unop]
  · intro x
    simpa only [MulEquiv.trans_apply, α, β, congr_rotationInclusion] using
      congrArg α (identification.rotationInclusion_unsignedEquiv_apply x)

end QPainleve.SignedClusterModularGroup
