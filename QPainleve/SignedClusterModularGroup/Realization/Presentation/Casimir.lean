/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.BoundaryExponent
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.MonomialImage
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.LinearAlgebra.Reflection
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Casimir
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# Casimir actions of marked toric presentations

A marked nodal model identifies the exchange kernel with the boundary orthogonal
and intertwines the Casimir action with signed Picard restriction. This comparison
also supplies the two cosets of the Casimir image, with a reflection along the
total boundary exponent representing the odd coset.

The comparison combines `exists_picardGroupEquivs_of_nodal_model` with
`GeometricRealization.existsUnique_exchangeKernelEquiv_of_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData
open scoped Pointwise RightActions

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "orth[" B "," D "]" => LinearMap.BilinForm.orthogonal B
  (Submodule.span ℤ (Set.range D))
local notation "exch[" E "]" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "total[" D "]" => ∑ j, D j
local notation "act[" E "]" => exchangeKernelAction ℂ E
local notation "unsignedImage[" E "]" =>
  MonoidHom.range (MonoidHom.comp act[E] (MonoidHom.op (clusterModularGroupInclusion ℂ E)))
local notation "coords[" B "," D "," e "]" =>
  MonoidHom.comp (MulEquiv.toMonoidHom (LinearEquiv.autCongr e))
    (Subgroup.subtype (LinearMap.BilinForm.isometryGroup
      (LinearMap.BilinForm.restrict B orth[B,D])))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r : ℕ}
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {n : ℕ}
  {E : SkewExchangeMatrix (Fin r)}

namespace CompleteToricPresentation

/-- The Picard and exchange-kernel identifications for the Casimir action of a marked
toric presentation. The exchange-kernel coordinates are the negatives of the
total exceptional coefficients. -/
@[ext]
structure CasimirActionComparison (Q : CompleteToricPresentation i b r L γ)
    (E : SkewExchangeMatrix (Fin r)) (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L) where
  /-- Picard pullback with its ordered branch sign. -/
  picardEquiv : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D
  /-- The exchange-kernel coordinates of boundary-orthogonal Picard classes. -/
  exchangeKernelEquiv : orth[B,D] ≃ₗ[ℤ] exch[E]
  /-- The coordinates are the negatives of the total exceptional coefficients. -/
  coe_exchangeKernelEquiv_apply (x : orth[B,D]) :
    (exchangeKernelEquiv x : Fin r → ℤ) = -(Q.inclusion x.val).2
  /-- Casimir transport is signed Picard restriction in exchange-kernel coordinates. -/
  exchangeKernelAction_eq :
    act[E] = coords[B,D,exchangeKernelEquiv].comp
      ((signedOrthogonalRestriction B D).comp picardEquiv.toMonoidHom)
  /-- The Picard sign has the unsigned point maps as its kernel. -/
  ker_sign : ((sign B D).comp picardEquiv.toMonoidHom).ker.unop =
    (clusterModularGroupInclusion ℂ E).range
  /-- A signed point map acting trivially on Casimirs is unsigned. -/
  ker_exchangeKernelAction_le :
    act[E].ker.unop ≤ (clusterModularGroupInclusion ℂ E).range

attribute [simp] CasimirActionComparison.coe_exchangeKernelEquiv_apply

/-- The intertwining formula evaluated on a signed point map, in pullback order. -/
theorem CasimirActionComparison.exchangeKernelAction_apply
    {Q : CompleteToricPresentation i b r L γ} {D : ZMod n → L}
    (A : Q.CasimirActionComparison E B D) (g : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ) :
    act[E] g = LinearEquiv.autCongr A.exchangeKernelEquiv
      (signedOrthogonalRestriction B D (A.picardEquiv g)).val := by
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply] using
    DFunLike.congr_fun A.exchangeKernelAction_eq g

/-- One marked nodal model of a primitive nef square-zero anticanonical cycle supplies
the signed Picard equivalence and its Casimir comparison in the specified presentation. -/
theorem nonempty_casimirActionComparison_of_nodal_model [NeZero n]
    (Q : CompleteToricPresentation i b r L γ)
    {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
    (href : Q.HasNodalModel c M)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(M.isEffectiveCartier_boundaryIdeal)
      classOf(M.isEffectiveCartier_boundaryIdeal) = 0) :
    Nonempty (Q.CasimirActionComparison E B
      (M.boundaryClass M.isEffectiveCartier_boundaryIdeal)) := by
  let P := Fan.rayChargeSeed b Q.rays hE
  obtain ⟨G, hGc⟩ := Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  let Θ := G.signedEquiv
  obtain ⟨e, ⟨he, hact, hCasimirKer⟩, _⟩ := existsUnique_exchangeKernelEquiv_of_presentation
    Q P (Fan.rayChargeSeed_form _ _ _) (Fan.rayChargeSeed_charge _ _ _)
    G.family (fun z ↦ (G.family z).isEffectiveCartier_boundaryIdeal)
    (G.hasNodalModel c) (fun z _ ↦ G.hasNodalModel z)
    (hGc.symm ▸ hnef) (hGc.symm ▸ hsq) (hGc.symm ▸ hprim) _ G.boundaryClass_eq
    Θ.toMonoidHom (fun w {_} _ _ R hR ↦ G.signedEquiv_apply_word (End.asHom w) R hR)
  refine ⟨⟨Θ, e, fun x ↦ neg_eq_iff_eq_neg.mp (he x).symm, ?_, G.sign_ker_unop, hCasimirKer⟩⟩
  simpa only [MonoidHom.comp_assoc] using hact

/-- A boundary-reversing Picard involution and the exchange-kernel comparison
for a marked presentation with primitive total boundary class. -/
@[ext]
structure CasimirReflection [NeZero n] (Q : CompleteToricPresentation i b r L γ)
    (E : SkewExchangeMatrix (Fin r)) (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L) where
  /-- The Picard and exchange-kernel identifications. -/
  comparison : Q.CasimirActionComparison E B D
  /-- The chosen boundary involution with its cut class. -/
  involution : CycleReversingInvolution B D
  total_mem_orthogonal : total[D] ∈ orth[B,D]
  isPrimitive_total : IsPrimitive total[D]
  isSymm : B.IsSymm
  isAddTorsionFree : IsAddTorsionFree L

namespace CasimirReflection

variable [NeZero n] {Q : CompleteToricPresentation i b r L γ} {D : ZMod n → L}
  (R : Q.CasimirReflection E B D)

/-- The primitive total boundary exponent in the exchange kernel. -/
def exponent : exch[E] :=
  R.comparison.exchangeKernelEquiv ⟨total[D], R.total_mem_orthogonal⟩

@[simp]
theorem coe_exponent : (R.exponent : Fin r → ℤ) = Q.totalBoundaryExponent D :=
  (R.comparison.coe_exchangeKernelEquiv_apply ⟨total[D], R.total_mem_orthogonal⟩).trans
    (Q.totalBoundaryExponent_def D).symm

/-- The total boundary exponent is primitive in the integral exchange kernel. -/
theorem isPrimitive_exponent : IsPrimitive R.exponent :=
  R.comparison.exchangeKernelEquiv.isPrimitive_iff.mpr
    (R.isPrimitive_total.of_map (g := orth[B,D].subtype))

/-- The reflecting form in exchange-kernel coordinates pairs with the cut class twice. -/
def reflectionForm : exch[E] →ₗ[ℤ] ℤ :=
  R.involution.orthogonalReflectionForm.comp
    (R.comparison.exchangeKernelEquiv.symm : exch[E] →ₗ[ℤ] orth[B,D])

@[simp]
theorem reflectionForm_apply (x : exch[E]) :
    R.reflectionForm x = 2 * B (R.comparison.exchangeKernelEquiv.symm x) R.involution.cutClass :=
  R.involution.orthogonalReflectionForm_apply _

/-- The reflecting form takes the primitive total boundary exponent to two. -/
@[simp high]
theorem reflectionForm_apply_exponent : R.reflectionForm R.exponent = 2 := by
  simpa only [reflectionForm, exponent, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using
    R.involution.orthogonalReflectionForm_apply_sum R.isSymm R.total_mem_orthogonal

/-- The Casimir reflection along the total boundary exponent. -/
def reflection : exch[E] ≃ₗ[ℤ] exch[E] :=
  Module.reflection R.reflectionForm_apply_exponent

theorem reflection_apply (x : exch[E]) :
    R.reflection x = x - R.reflectionForm x • R.exponent :=
  Module.reflection_apply x R.reflectionForm_apply_exponent

@[simp]
theorem reflection_apply_exponent : R.reflection R.exponent = -R.exponent :=
  Module.reflection_apply_self R.reflectionForm_apply_exponent

/-- The Casimir reflection is an involution. -/
theorem involutive_reflection : Function.Involutive R.reflection :=
  Module.involutive_reflection R.reflectionForm_apply_exponent

/-- Applying the Casimir reflection twice fixes every exchange-kernel vector. -/
@[simp]
theorem reflection_reflection (x : exch[E]) : R.reflection (R.reflection x) = x :=
  R.involutive_reflection x

/-- The inverse of the Casimir reflection is the reflection itself. -/
@[simp]
theorem reflection_symm : R.reflection.symm = R.reflection :=
  Module.reflection_symm R.reflectionForm_apply_exponent

/-- The Casimir reflection induces the identity modulo the total boundary exponent. -/
@[simp high]
theorem mkQ_reflection_apply (x : exch[E]) :
    (ℤ ∙ R.exponent).mkQ (R.reflection x) = (ℤ ∙ R.exponent).mkQ x :=
  Module.mkQ_reflection_apply R.reflectionForm_apply_exponent x

/-- The signed point map of the chosen Picard involution acts by the Casimir reflection. -/
@[simp]
theorem exchangeKernelAction_picardEquiv_symm :
    act[E] (R.comparison.picardEquiv.symm R.involution.element) = R.reflection :=
  exchangeKernelAction_picardEquiv_symm_cycleReversingInvolution
    R.comparison.picardEquiv R.comparison.exchangeKernelEquiv R.comparison.exchangeKernelAction_eq
    R.involution R.total_mem_orthogonal
    (R.involution.orthogonalReflectionForm_apply_sum R.isSymm R.total_mem_orthogonal)

private theorem range_eq_disjoint_union :
    let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[E]
    (↑(act[E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) =
      unsigned ∪ (unsigned <• R.reflection) ∧ Disjoint unsigned (unsigned <• R.reflection) := by
  let : IsAddTorsionFree L := R.isAddTorsionFree
  simpa only [R.exchangeKernelAction_picardEquiv_symm] using
    range_exchangeKernelAction_eq_disjoint_union
      R.comparison.picardEquiv R.comparison.exchangeKernelEquiv R.comparison.exchangeKernelAction_eq
      R.comparison.ker_sign R.total_mem_orthogonal R.isPrimitive_total.ne_zero
      R.involution.element (by simp)

/-- The signed Casimir image is the union of the unsigned image and its right coset
by the Casimir reflection. -/
theorem range_exchangeKernelAction :
    let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[E]
    (↑(act[E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• R.reflection) :=
  R.range_eq_disjoint_union.1

/-- The reflection coset is disjoint from the unsigned Casimir image. -/
theorem disjoint_unsignedImage :
    let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[E]
    Disjoint unsigned (unsigned <• R.reflection) :=
  R.range_eq_disjoint_union.2

end CasimirReflection

/-- A marked nodal model of a primitive nef square-zero anticanonical cycle supplies
a Casimir reflection along its total boundary exponent. Its involution lifts to the
signed cluster modular group and supplies the odd coset of the Casimir image. -/
theorem nonempty_casimirReflection_of_nodal_model [NeZero n]
    (Q : CompleteToricPresentation i b r L γ)
    {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
    (href : Q.HasNodalModel c M)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(M.isEffectiveCartier_boundaryIdeal)))
    (hnef : (classOf(M.isEffectiveCartier_boundaryIdeal)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(M.isEffectiveCartier_boundaryIdeal)
      classOf(M.isEffectiveCartier_boundaryIdeal) = 0) :
    Nonempty (Q.CasimirReflection E B (M.boundaryClass M.isEffectiveCartier_boundaryIdeal)) := by
  obtain ⟨A⟩ := Q.nonempty_casimirActionComparison_of_nodal_model href hE hprim hnef hsq
  let : Scheme.IsRationalOver (M.surface ↘ S) := href.isRationalOver
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Module.Free ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.free_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv M.picardMarking.symm
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  let hD := M.isEffectiveCartier_boundaryIdeal
  obtain ⟨s⟩ := M.nonempty_cycleReversingInvolution
    (congrArg Inv.inv (href.canonicalClass hD)) hnef hsq hprim
  have hPrimitive : IsPrimitive (total[M.boundaryClass hD]) :=
    M.picardMarking.isPrimitive_iff.mp (by rwa [M.picardMarking_sum_boundaryClass])
  exact ⟨{
    comparison := A
    involution := s
    total_mem_orthogonal := BoundaryCycle.sum_mem_orthogonal
      (M.intersectionForm_boundaryClass hD hnef hsq)
    isPrimitive_total := hPrimitive
    isSymm := M.isSymm
    isAddTorsionFree := inferInstance }⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
