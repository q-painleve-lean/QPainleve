/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.MonomialImage
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.BoundaryExponent
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
local notation "boundary[" M "]" =>
  Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
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

end CompleteToricPresentation

namespace GeometricRealization

/-- On a marked toric presentation of a primitive nef square-zero cycle, a reversing loop
acts by reflection along the primitive total boundary exponent and acts trivially on the
quotient by that exponent. The full Casimir image consists of the unsigned image and its
disjoint right coset by this reflection. The exponent entries are the multiplicities of the
total boundary transform at the ordered centers. -/
theorem exists_exchangeKernelAction_reflection_of_presentation [NeZero n]
    (Q : CompleteToricPresentation i b r L γ)
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
    (href : Q.HasNodalModel c M) (hD : boundary[M].IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD)))
    (hnef : (classOf(hD)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0) :
    let D := M.boundaryClass hD
    ∃ (A : Q.CasimirActionComparison E B D)
      (hδ : total[D] ∈ orth[B,D]) (a : L) (s : signedBoundaryIsometryGroup B D),
      let v := A.exchangeKernelEquiv ⟨total[D], hδ⟩
      IsPrimitive v ∧
      (letI := Q.complete.nonempty_cones
       letI := Q.prestable
       letI := Q.neZero
       ∀ p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M,
         (v : Fin r → ℤ) = fun j ↦ p.totalBoundaryRayMultiplicity hD (Q.rays j)) ∧
      let ℓ := ((2 : ℤ) • (B.flip a).comp orth[B,D].subtype).comp
        (A.exchangeKernelEquiv.symm : exch[E] →ₗ[ℤ] orth[B,D])
      ∃ hℓ : ℓ v = 2,
        let q := Module.reflection hℓ
        let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[E]
        sign B D s = -1 ∧ s * s = 1 ∧ act[E] (A.picardEquiv.symm s) = q ∧
          (↑(act[E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
          Disjoint unsigned (unsigned <• q) ∧
          ∀ x, (ℤ ∙ v).mkQ (q x) = (ℤ ∙ v).mkQ x := by
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  obtain ⟨A⟩ := Q.nonempty_casimirActionComparison_of_nodal_model href hE hprim hnef hsq
  let : Scheme.IsRationalOver (M.surface ↘ S) := href.isRationalOver
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : B.IsPerfPair := M.isPerfPair_of_isRationalOver
  let : Module.Free ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass M.surface)) :=
    M.surface.finite_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv M.picardMarking.symm
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ M.picardMarking.symm.surjective
  have hpair (x y : L) := (M.intersectionBilinForm_picardMarking x y).symm.trans
    (Chow.intersectionBilinForm_apply ..)
  have hSymm : B.IsSymm := ⟨fun x y ↦
    (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hPrimitive : IsPrimitive (total[M.boundaryClass hD]) :=
    M.picardMarking.isPrimitive_iff.mp (by rwa [M.picardMarking_sum_boundaryClass])
  obtain ⟨hδ, a, s, hℓ, hreflection⟩ :=
    exists_exchangeKernelAction_reflection A.picardEquiv A.exchangeKernelEquiv
      A.exchangeKernelAction_eq A.ker_sign hSymm
      (M.intersectionForm_boundaryClass hD hnef hsq) hPrimitive
      (M.isCharacteristic_sum_boundaryClass hD (congrArg Inv.inv (href.canonicalClass hD)))
  refine ⟨A, hδ, a, s, A.exchangeKernelEquiv.isPrimitive_iff.mpr
    (hPrimitive.of_map (g := orth[B,M.boundaryClass hD].subtype)), ?_, hℓ, hreflection⟩
  intro p
  rw [A.coe_exchangeKernelEquiv_apply, ← Q.totalBoundaryExponent_def]
  exact Q.totalBoundaryExponent_eq_totalBoundaryRayMultiplicity p _ rfl

end GeometricRealization

end QPainleve.SignedClusterModularGroup
