/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Casimir
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# Images of signed cluster actions on Casimir monomials

The Picard equivalence transports the boundary rotation image to the unsigned Casimir image.
The full Casimir image contains one further right coset, represented by the restriction of a
signed Picard reflection. The two cosets act with opposite signs on the total boundary exponent.
For a marked toric presentation the signed Picard equivalence and exchange-kernel comparison
supply the geometric actions. The Picard equivalence is taken from
`CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`.
The reflection is Mathlib's `Module.reflection`, transported from
`SignedBoundaryIsometryGroup.exists_signedOrthogonalRestriction_eq_reflection`.
-/

public section

open MulOpposite
open scoped Pointwise RightActions

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open Cluster SignedBoundaryIsometryGroup

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : SkewExchangeMatrix ι}
  {L : Type*} [AddCommGroup L] {n : ℕ} {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}

local notation "orth[" B "," D "]" => LinearMap.BilinForm.orthogonal B
  (Submodule.span ℤ (Set.range D))
local notation "exch[" E "]" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "total[" D "]" => ∑ i, D i
local notation "restr[" B "," D "]" => signedOrthogonalRestriction B D
local notation "incl[" k "," E "]" => MonoidHom.op (clusterModularGroupInclusion k E)
local notation "act[" k "," E "]" => exchangeKernelAction k E
local notation "unsignedImage[" k "," E "]" =>
  MonoidHom.range (MonoidHom.comp act[k,E] incl[k,E])

variable (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
  (e : orth[B,D] ≃ₗ[ℤ] exch[E])

local notation "coords[" B "," D "," a "]" =>
  MonoidHom.comp (MulEquiv.toMonoidHom (LinearEquiv.autCongr a))
    (Subgroup.subtype (LinearMap.BilinForm.isometryGroup
      (LinearMap.BilinForm.restrict B orth[B,D])))

variable (hCasimir : act[k,E] =
    MonoidHom.comp coords[B,D,e] (MonoidHom.comp restr[B,D] Θ.toMonoidHom))
  (hker : ((sign B D).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion k E).range)

omit [Fintype ι] in
include hker in
private theorem range_picardEquiv_comp_unsignedInclusion :
    (Θ.toMonoidHom.comp incl[k,E]).range = (rotationInclusion B D).range := by
  have hop : (incl[k,E]).range = (clusterModularGroupInclusion k E).range.op := by
    ext f
    simp only [MonoidHom.mem_range, Subgroup.mem_op, MonoidHom.op_apply_apply]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g.unop, by simpa only [Function.comp_apply, unop_op] using congrArg unop hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨op g, by simpa only [Function.comp_apply, unop_op, op_unop] using congrArg op hg⟩
  rw [MonoidHom.range_comp, hop, ← hker, Subgroup.op_unop, range_rotationInclusion,
    ← MonoidHom.comap_ker]
  exact Subgroup.map_comap_eq_self_of_surjective Θ.surjective _

include hCasimir hker in
/-- The unsigned Casimir image is the image of the boundary rotations, restricted to the
boundary orthogonal and written in exchange-kernel coordinates. -/
theorem range_unsignedExchangeKernelAction_eq_rotationImage :
    unsignedImage[k,E] = (((restr[B,D]).comp (rotationInclusion B D)).range).map coords[B,D,e] := by
  rw [MonoidHom.range_comp (restr[B,D]), ← range_picardEquiv_comp_unsignedInclusion Θ hker]
  simp only [hCasimir, MonoidHom.range_comp, Subgroup.map_map, MonoidHom.comp_assoc]

include hCasimir in
private theorem exchangeKernelAction_picardEquiv_symm (s : signedBoundaryIsometryGroup B D) :
    act[k,E] (Θ.symm s) = LinearEquiv.autCongr e (restr[B,D] s).val := by
  rw [hCasimir]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Subgroup.subtype_apply]

variable [NeZero n]

include hCasimir in
/-- A signed cluster pullback scales the total boundary exponent by the sign of its marked
Picard action. -/
theorem exchangeKernelAction_apply_boundary_sum (hδ : total[D] ∈ orth[B,D])
    (g : (SignedClusterModularGroup k E)ᵐᵒᵖ) :
    act[k,E] g (e ⟨total[D], hδ⟩) = sign B D (Θ g) • e ⟨total[D], hδ⟩ := by
  have hg := DFunLike.congr_fun hCasimir g
  rw [hg]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply,
    signedOrthogonalRestriction_apply_sum, Units.smul_def, map_smul]

include hCasimir hker in
/-- The signed Casimir image is the disjoint union of the unsigned image and its right coset
by the Casimir action of any lift with negative Picard sign. -/
theorem range_exchangeKernelAction_eq_disjoint_union [IsAddTorsionFree L]
    (hδ : total[D] ∈ orth[B,D]) (hδ₀ : total[D] ≠ 0)
    (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1) :
    let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[k,E]
    let q := act[k,E] (Θ.symm s)
    (↑(act[k,E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
      Disjoint unsigned (unsigned <• q) := by
  dsimp only
  have hW := range_unsignedExchangeKernelAction_eq_rotationImage Θ e hCasimir hker
  have hfull : (act[k,E]).range = ((restr[B,D]).range).map coords[B,D,e] := by
    rw [hCasimir, MonoidHom.range_comp coords[B,D,e], MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective Θ.toMonoidHom Θ.surjective, Subgroup.map_top]
  have hC : Function.Injective coords[B,D,e] :=
    (LinearEquiv.autCongr e).injective.comp Subtype.val_injective
  have hq : act[k,E] (Θ.symm s) = coords[B,D,e] (restr[B,D] s) :=
    exchangeKernelAction_picardEquiv_symm Θ e hCasimir s
  rw [hfull, hW, Subgroup.coe_map, Subgroup.coe_map, hq, ← Set.image_op_smul_distrib]
  constructor
  · rw [← Set.image_union, range_signedOrthogonalRestriction_eq_union B D s hs]
  · exact Set.disjoint_image_of_injective hC (disjoint_rotationRange_rightCoset hδ hδ₀ s hs)

variable {Θ e}

include hCasimir in
/-- For a boundary of length one or two, the central sign change acts on the exchange kernel
by negation. -/
theorem exchangeKernelAction_picardEquiv_symm_centralSign (hn : n ≤ 2) (x : exch[E]) :
    act[k,E] (Θ.symm (centralSign B D hn)) x = -x := by
  rw [exchangeKernelAction_picardEquiv_symm Θ e hCasimir,
    LinearEquiv.autCongr_apply_apply, signedOrthogonalRestriction_centralSign_apply, map_neg,
    LinearEquiv.apply_symm_apply]

variable (Θ e)

include hCasimir hker in
/-- For a unimodular symmetric cycle lattice with primitive characteristic total class,
a signed Picard involution acts on the exchange kernel by reflection along the total
boundary exponent. This reflection represents the odd coset of the unsigned Casimir
image and acts trivially modulo the total boundary exponent. -/
theorem exists_exchangeKernelAction_reflection [Module.Free ℤ L] [Module.Finite ℤ L]
    [B.IsPerfPair] (hSymm : B.IsSymm)
    (hGram : ∀ i j : ZMod n, B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive total[D]) (hCharacteristic : B.IsCharacteristic total[D]) :
    ∃ (hδ : total[D] ∈ orth[B,D]) (a : L) (s : signedBoundaryIsometryGroup B D),
      let v := e ⟨total[D], hδ⟩
      let ℓ := ((2 : ℤ) • (B.flip a).comp (orth[B,D]).subtype).comp
        (e.symm : exch[E] →ₗ[ℤ] orth[B,D])
      ∃ hℓ : ℓ v = 2,
        let q := Module.reflection hℓ
        let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[k,E]
        sign B D s = -1 ∧ s * s = 1 ∧ act[k,E] (Θ.symm s) = q ∧
          (↑(act[k,E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
          Disjoint unsigned (unsigned <• q) ∧
          ∀ x, (ℤ ∙ v).mkQ (q x) = (ℤ ∙ v).mkQ x := by
  obtain ⟨hδ, a, s, hℓ, hs, hss, hreflect, -⟩ :=
    exists_signedOrthogonalRestriction_eq_reflection B D hSymm hGram hPrimitive hCharacteristic
  let v := e ⟨total[D], hδ⟩
  let ℓ := ((2 : ℤ) • (B.flip a).comp (orth[B,D]).subtype).comp (e.symm : exch[E] →ₗ[ℤ] orth[B,D])
  have hℓ' : ℓ v = 2 := by
    simpa only [ℓ, v, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using hℓ
  have hq : act[k,E] (Θ.symm s) = Module.reflection hℓ' := by
    rw [exchangeKernelAction_picardEquiv_symm Θ e hCasimir, hreflect]
    ext x : 1
    simp only [LinearEquiv.autCongr_apply_apply, Module.reflection_apply, map_sub, map_smul,
      LinearEquiv.apply_symm_apply, ℓ, v, LinearMap.comp_apply, LinearEquiv.coe_coe]
  let : HasUniqueDiv L := HasUniqueDiv.of_isTorsionFree ℤ L
  obtain ⟨himage, hdisjoint⟩ :=
    range_exchangeKernelAction_eq_disjoint_union Θ e hCasimir hker hδ hPrimitive.ne_zero s hs
  refine ⟨hδ, a, s, hℓ', hs, hss, hq, ?_, ?_, ?_⟩
  · simpa only [hq] using himage
  · simpa only [hq] using hdisjoint
  · intro x
    rw [Module.reflection_apply, map_sub, sub_eq_self, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

section Presentation

open AlgebraicGeometry CategoryTheory Quiver
open QPainleve.CharacterTorus
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "boundary[" M "]" =>
  Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r : ℕ}
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {n : ℕ} [NeZero n]
  {E : SkewExchangeMatrix (Fin r)}

/-- On a marked toric presentation of a primitive nef square-zero cycle, the exchange
kernel has integral charge coordinates. The signed Casimir image consists of the
boundary rotation image and its disjoint right coset by the action of a reversing loop.
The reversing action is reflection along the total boundary exponent and fixes its
quotient. This exponent is primitive and its entries are the multiplicities of the
total boundary transform on the rays of the ordered centers. For a cycle of length
at most two the central sign acts by negation.
The exponent comparison computes monomial pullback via `Cluster.exchangeKernelAction_monomial`. -/
theorem exists_exchangeKernelAction_reflection_of_presentation
    (Q : CompleteToricPresentation i b r L γ)
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}
    (href : Q.HasNodalModel c M) (hD : boundary[M].IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD)))
    (hnef : (classOf(hD)).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0) :
    let D := M.boundaryClass hD
    ∃ (Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B D)
      (e : orth[B,D] ≃ₗ[ℤ] exch[E]),
      (∀ x, (Q.inclusion x.val).2 = -(e x : Fin r → ℤ)) ∧
      act[ℂ,E] = coords[B,D,e].comp (restr[B,D].comp Θ.toMonoidHom) ∧
      ((sign B D).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      (act[ℂ,E]).ker.unop ≤ (clusterModularGroupInclusion ℂ E).range ∧
      unsignedImage[ℂ,E] = ((restr[B,D].comp (rotationInclusion B D)).range).map coords[B,D,e] ∧
      (∀ (hδ : total[D] ∈ orth[B,D]) g,
        act[ℂ,E] g (e ⟨total[D], hδ⟩) = sign B D (Θ g) • e ⟨total[D], hδ⟩) ∧
      (∀ (hn : n ≤ 2) x, act[ℂ,E] (Θ.symm (centralSign B D hn)) x = -x) ∧
      ∃ (hδ : total[D] ∈ orth[B,D]) (a : L) (s : signedBoundaryIsometryGroup B D),
        let v := e ⟨total[D], hδ⟩
        IsPrimitive v ∧
        (letI := Q.complete.nonempty_cones
         letI := Q.prestable
         letI := Q.neZero
         ∀ p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M,
           (v : Fin r → ℤ) = fun j ↦ p.totalBoundaryRayMultiplicity hD (Q.rays j)) ∧
        let ℓ := ((2 : ℤ) • (B.flip a).comp orth[B,D].subtype).comp
          (e.symm : exch[E] →ₗ[ℤ] orth[B,D])
        ∃ hℓ : ℓ v = 2,
          let q := Module.reflection hℓ
          let unsigned : Set (exch[E] ≃ₗ[ℤ] exch[E]) := unsignedImage[ℂ,E]
          sign B D s = -1 ∧ s * s = 1 ∧ act[ℂ,E] (Θ.symm s) = q ∧
            (↑(act[ℂ,E]).range : Set (exch[E] ≃ₗ[ℤ] exch[E])) = unsigned ∪ (unsigned <• q) ∧
            Disjoint unsigned (unsigned <• q) ∧
            ∀ x, (ℤ ∙ v).mkQ (q x) = (ℤ ∙ v).mkQ x := by
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  obtain ⟨F, hF, hmark, Θ, _, hM, hmodels, hΘ, hker, _⟩ :=
    Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  subst M
  let M := F c
  obtain ⟨e, ⟨he, hact, hCasimirKer⟩, _⟩ := existsUnique_exchangeKernelEquiv_of_presentation
    Q P hform hcharge F hF (hmodels c) (fun d _ ↦ hmodels d) hnef hsq hprim _ hmark
    Θ.toMonoidHom (fun w {_} _ _ R hR ↦ (hΘ (End.asHom w)).2 R hR)
  have hCasimir : act[ℂ,E] =
      coords[B,M.boundaryClass hD,e].comp (restr[B,M.boundaryClass hD].comp Θ.toMonoidHom) := by
    simpa only [MonoidHom.comp_assoc] using hact
  refine ⟨Θ, e, he, hCasimir, hker, hCasimirKer,
    range_unsignedExchangeKernelAction_eq_rotationImage Θ e hCasimir hker,
    exchangeKernelAction_apply_boundary_sum Θ e hCasimir,
    exchangeKernelAction_picardEquiv_symm_centralSign hCasimir, ?_⟩
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
    exists_exchangeKernelAction_reflection Θ e hCasimir hker hSymm
      (M.intersectionForm_boundaryClass hD hnef hsq) hPrimitive
      (M.isCharacteristic_sum_boundaryClass hD (congrArg Inv.inv (href.canonicalClass hD)))
  refine ⟨hδ, a, s, e.isPrimitive_iff.mpr (hPrimitive.of_map
    (g := orth[B,M.boundaryClass hD].subtype)), ?_, hℓ, hreflection⟩
  intro p
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  have hw := congrArg Prod.snd (p.inclusion_sum_boundaryClass hD)
  rw [he ⟨_, hδ⟩, Fan.markedBoundaryMap_apply] at hw
  exact neg_injective hw

end Presentation

end QPainleve.SignedClusterModularGroup.GeometricRealization
