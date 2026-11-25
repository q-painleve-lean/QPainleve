/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.LinearAlgebra.BilinearForm.Prod
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Kernel
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# The central sign involution of the eleven-vertex seed

The ordered triangle blowups and the two nodal blowdowns give a reference
fiber in the original seed basis. The faithful signed Picard action sends
`involutionWord` to the identity isometry with negative branch sign.
On the single boundary component the forward index is unique, so the
comparison uses the sign and the negation action on the exchange kernel.
The comparisons use `chargeKernelAction_eq_signedOrthogonalRestriction` and
`boundary_isometry_ext`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MulOpposite Multiplicative Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open QPainleve.SignedClusterModularGroup QPainleve.SignedClusterModularGroup.GeometricRealization
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan

namespace QPainleve.ElevenVertex

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers" => Over.mk (structureMap ℂ (Fin 11 → ℤ))
local notation "XTor" => scheme ℂ (Fin 11 →₀ ℤ)
local notation "b" => Pi.basisFun ℤ (Fin 2)
local notation "Φ" => Fan.projectiveSpace b (isIntegralLattice_intCast 2)
local notation "planeLattice" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "params[" c "]" => (fun j : Fin 11 ↦ χ[c] (ofAdd (Pi.single j 1)))
local notation "Γ" => SignedClusterModularGroup ℂ exchangeMatrix
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ exchangeMatrix (End.of w))

private theorem eq_centralSign_of_signedRestriction
    {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    {H : LinearMap.BilinForm ℤ L} (hSymm : H.IsSymm) (hnondeg : H.Nondegenerate)
    {d : ZMod 1 → L} (hgram : ∀ j k, H (d j) (d k) = (-2 : ℤ) * (if j = k then 1 else 0) +
      (if k = j + 1 then 1 else 0) + (if k = j - 1 then 1 else 0))
    (g : signedBoundaryIsometryGroup H d)
    (hsign : sign H d g = -1)
    (horth : ∀ x : H.orthogonal (Submodule.span ℤ (Set.range d)),
      (signedOrthogonalRestriction H d g).val x = -x) :
    g = centralSign H d (by decide) := by
  have hone (x : L) : (1 : L ≃ₗ[ℤ] L) x = x := (rfl)
  apply Subtype.ext
  apply Prod.ext
  · rw [coe_centralSign, ← toIsometry_apply]
    apply H.isometryGroupEquivIsometryEquiv.injective
    refine boundary_isometry_ext (D := d) hSymm hnondeg.1
      (BoundaryCycle.span_sup_orthogonal_rat hgram hSymm hnondeg) ?_ ?_
    · intro j
      obtain ⟨p, hp⟩ := exists_indexPerm H d g
      simpa only [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv,
        OneMemClass.coe_one, hone, Subsingleton.elim (p j) j] using hp j
    · intro x hx
      have heq := congrArg Subtype.val (horth ⟨x, hx⟩)
      simpa only [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv,
        OneMemClass.coe_one, hone, coe_signedOrthogonalRestriction_apply,
        hsign, Units.neg_smul, one_smul, Submodule.coe_neg, neg_inj] using heq
  · simpa only [coe_centralSign, SignedBoundaryIsometryGroup.sign_apply] using hsign

private theorem exists_marked_reference (u : Fin 11 → ℂˣ) :
    ∃ (L : Type) (_ : AddCommGroup L) (H : LinearMap.BilinForm ℤ L)
      (_ : Module.Free ℤ L) (_ : Module.Finite ℤ L) (_ : H.IsPerfPair)
      (Q : CompleteToricPresentation planeLattice b 11 L Empty)
      (c : Point Centers) (M : MarkedSurface ℂ 1 H XTor)
      (hD : D[M].IsEffectiveCartier),
      H.IsSymm ∧ params[c] = u ∧ (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = planeCenterRay) ∧
        Q.HasNodalModel c M ∧ IsPrimitive (Additive.ofMul classOf(hD)) ∧
        classOf(hD).IsNef ℂ (M.surface ↘ S) ∧
        Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0 := by
  obtain ⟨W, s, hs, D, hD, _, hpre, _, _, A, U, R, a, _, hW, hproj, hrat, _, _, _,
    hprim, hnef, hsq, hR, hbase, hker, _, _, _, _⟩ := exists_eleven_vertex_toric_presentation u
  let : W.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hs
  let : IsIntegral W := hW
  let : W.IsProjectiveOver ℂ := hproj
  let : IsRationalOver (W ↘ S) := hrat
  let : PrestableFamily (D.subscheme ↘ S) := hpre
  let : (Iso.refl D.subscheme).hom.IsOver S :=
    inferInstanceAs ((𝟙 D.subscheme : D.subscheme ⟶ D.subscheme).IsOver S)
  let A' := (Iso.refl D.subscheme).mapNodalCycleNumbering A
    (q := (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus))
  let : Module.Free ℤ (Additive (LineBundleClass W)) := W.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass W)) := W.finite_picard_of_isRationalOver ℂ
  let H₀ := Chow.intersectionBilinForm ℂ W
  let e := (Module.finBasis ℤ (Additive (LineBundleClass W))).equivFun.symm
  let H : LinearMap.BilinForm ℤ (Fin (Module.finrank ℤ (Additive (LineBundleClass W))) → ℤ) :=
    H₀.compl₁₂ e.toLinearMap e.toLinearMap
  let μ : H.IsometryEquiv H₀ := ⟨e, fun _ _ ↦ rfl⟩
  obtain ⟨A'', Q, c, f, _, hparams, hrays, hm⟩ :=
    exists_marked_reference_fiber_of_ordered_towers_fixed_basis
      (isRegular_projectiveSpace b (isIntegralLattice_intCast 2))
      (isComplete_projectiveSpace b (isIntegralLattice_intCast 2))
      planeCenterRay u hR a hbase hker hD A' μ
  let M := MarkedSurface.ofBoundary D A'' μ f
  let hCart := M.isEffectiveCartier_boundaryIdeal
  let : IsRationalOver (M.surface ↘ S) := hm.isRationalOver
  have hclass : classOf(hCart) = classOf(hD) :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr hCart hD
      (MarkedSurface.ofBoundary_ker ..))
  refine ⟨_, _, H, inferInstance, inferInstance, M.isPerfPair_of_isRationalOver, Q, c, M, hCart,
    ?_, hparams, hrays, hm, hclass.symm ▸ hprim, hclass.symm ▸ hnef, hclass.symm ▸ hsq⟩
  exact ⟨fun x y ↦ by
    simp only [H, H₀, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      Chow.intersectionBilinForm_apply, Chow.classIntersectionNumber_comm]⟩

private def planeChargeSeed : ChargeSeed exchangeMatrix (Fin 2 → ℤ) :=
  ⟨(b).detDualEquiv.toLinearMap, chargeMap, (b).detDualEquiv_self,
    exchangeMatrix_eq_chargeExchangeMatrix.symm⟩

private theorem planeChargeSeed_charge_eq
    {L : Type} [AddCommGroup L] {Q : CompleteToricPresentation planeLattice b 11 L Empty}
    (hrays : ∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = planeCenterRay) :
    planeChargeSeed.charge = Fan.rayChargeMap Q.rays := by
  obtain ⟨hfan, hr⟩ := hrays
  have heq {Ψ : Fan planeLattice} (h : Ψ = Φ) (s : Fin 11 → Ψ.Ray) :
      Fan.rayChargeMap (h ▸ s) = Fan.rayChargeMap s := by
    subst Ψ
    rfl
  rw [← heq hfan Q.rays, hr, rayChargeMap_planeCenterRay]
  rfl

section Involution

variable {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation planeLattice b 11 L Empty)
  {M : Point Centers → MarkedSurface ℂ 1 H XTor}

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Cz" => Path.centerPartialMap ℂ involutionWord planeChargeSeed

private theorem signedOrthogonalRestriction_of_involution_realization [H.IsPerfPair]
    (hc : planeChargeSeed.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ a, Q.HasNodalModel a (M a)) (c : Point Centers)
    (hD : ∀ a, D[M a].IsEffectiveCartier)
    (d : ZMod 1 → L) (hmark : ∀ a j, (M a).boundaryClass (hD a) j = d j)
    (R : GeometricRealization M M Cz (involutionWord.xRationalMap ℂ))
    (x : H.orthogonal (Submodule.span ℤ (Set.range d))) :
    (signedOrthogonalRestriction H d (R.toSignedBoundaryIsometry d hD hmark)).val x = -x := by
  classical
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
    rw [Q.fan.algebraicRealization_over]
    simpa using Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular
  let : IsRationalOver (Q.fan.algebraicRealization ↘ S) := Q.isRationalOver_fan
  let hperf := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ Q.fan.algebraicRealization
  let G : LinearMap.BilinForm ℤ (Fin 11 → ℤ) := dotProductBilin ℤ ℤ
  let : G.IsPerfPair := dotProductBilin_isPerfPair ℤ (Fin 11)
  have hneg : (-G).IsPerfPair := by
    convert LinearMap.IsPerfPair.compl₁₂ G (LinearEquiv.neg ℤ) (LinearEquiv.refl ℤ _) using 1
    ext x y
    simp
  let := LinearMap.BilinForm.isPerfPair_prod_iff.mpr ⟨hperf, hneg⟩
  choose p hp using fun a ↦ (models a).exists_isNodalContraction (hD a)
  obtain ⟨e, he, _⟩ := (p c).existsUnique_markedBoundaryOrthogonalEquivChargeKernel (hp c)
    (hD c) (funext (hmark c))
  let u := Q.fan.rayEquivOfNodalCycleNumbering Q.regular Q.cycle
  have hu (j : ZMod Q.length) : u j = Q.rayOrder j := by
    apply (Q.fan.boundaryNormalizationComponentEquiv Q.regular).injective
    rw [Fan.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering, Q.component_eq]
  obtain ⟨_, _, _, hn⟩ :=
    Q.fan.exists_positive_ray_numbering_of_nodalCycleNumbering b Q.regular Q.complete Q.cycle
  have hker : exchangeMatrix.matrix.mulVecLin.ker = planeChargeSeed.charge.ker :=
    exchangeKernel_eq_chargeKernel
  have hcompare := chargeKernelAction_eq_signedOrthogonalRestriction u
    (fun j ↦ (Q.cycle.component_apply j).symm.trans
      (Fan.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering ..).symm)
    (fun j ↦ by simpa only [hu] using (Q.positive j).1)
    (fun j ↦ let ⟨σ, h₀, h₁, hpoint⟩ := hn j; ⟨σ.val, h₀, h₁, hpoint⟩)
    d hD hmark involutionWord R (involutionWord.centerPartialMap_hom (K := ℂ) planeChargeSeed)
    planeChargeSeed hc hker e he (U := Set.univ) (fun _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩)
    (fun a _ ↦ (hp a).genus_zero) (fun a _ ↦ ⟨p a⟩)
  have hx := DFunLike.congr_fun hcompare (e x)
  apply e.injective
  simpa only [chargeKernelAction_apply, exchangeKernelAction_op_loop,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply,
    involutionWord_exchangeKernelEquiv_apply, map_neg, LinearEquiv.apply_symm_apply] using hx.symm

end Involution

/-- For any ordered center parameters, the plane model gives a marked one-component
reference fiber whose faithful signed Picard action sends the specified odd loop
to the central sign element. Its values on loops are the marked pullbacks of their
geometric realizations, with sign given by inversion parity. -/
theorem exists_eleven_vertex_signedPicardHom (u : Fin 11 → ℂˣ) :
    ∃ (L : Type) (_ : AddCommGroup L) (H : LinearMap.BilinForm ℤ L)
      (Q : CompleteToricPresentation planeLattice b 11 L Empty)
      (c : Point Centers) (M : Point Centers → MarkedSurface ℂ 1 H XTor)
      (hD : ∀ a, D[M a].IsEffectiveCartier),
      params[c] = u ∧ (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = planeCenterRay) ∧
      ∃ (hfamily : ∀ a, Q.HasNodalModel a (M a) ∧
          (M a).boundaryClass (hD a) = (M c).boundaryClass (hD c))
        (ρ : Γᵐᵒᵖ →* signedBoundaryIsometryGroup H ((M c).boundaryClass (hD c))),
        Function.Injective ρ ∧
        ρ eval[involutionWord] = centralSign H ((M c).boundaryClass (hD c)) (by decide) ∧
        ∀ (w : Word exchangeMatrix exchangeMatrix), sign H ((M c).boundaryClass (hD c))
            (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
          ∀ {C : (Centers).left.PartialMap (Centers).left} [IsDominant C.hom]
            [C.IsOver (Centers).hom (Centers).hom]
            (R : GeometricRealization M M C (w.xRationalMap ℂ)),
            ρ eval[w] = R.toSignedBoundaryIsometry ((M c).boundaryClass (hD c)) hD
              (fun a j ↦ congrFun (hfamily a).2 j) := by
  obtain ⟨L, _, H, _, _, _, Q, c, M₀, hD₀, hSymm, hparams, hrays, hm₀, hprim, hnef, hsq⟩ :=
    exists_marked_reference u
  obtain ⟨M, hD, hMc, hM⟩ := Q.exists_marked_family_of_nodal_model hm₀ hD₀
  have hfamily (a : Point Centers) :
      Q.HasNodalModel a (M a) ∧ (M a).boundaryClass (hD a) = (M c).boundaryClass (hD c) := by
    refine ⟨(hM a).1, (hM a).2.trans ?_⟩
    cases hMc
    rfl
  let d := (M c).boundaryClass (hD c)
  have hmark (a : Point Centers) (j : ZMod 1) : (M a).boundaryClass (hD a) j = d j :=
    congrFun (hfamily a).2 j
  have hprim' : IsPrimitive (Additive.ofMul classOf(hD c)) := by cases hMc; exact hprim
  have hnef' : classOf(hD c).IsNef ℂ ((M c).surface ↘ S) := by cases hMc; exact hnef
  have hsq' : Chow.classIntersectionNumber ℂ (M c).surface classOf(hD c) classOf(hD c) = 0 := by
    cases hMc
    exact hsq
  let P := planeChargeSeed
  have hc := planeChargeSeed_charge_eq hrays
  let : IsRationalOver ((M c).surface ↘ S) := (hfamily c).1.isRationalOver
  have hcan := congrArg Inv.inv ((hfamily c).1.canonicalClass (hD c))
  obtain ⟨ρ, ⟨hρ, _⟩, _⟩ := existsUnique_signedPicardHom_of_presentation
    P Q rfl hc M (fun _ ↦ (hfamily _).1) (hfamily c).1 hD hnef' hsq' hcan hprim' d hmark
  have hinj := ρ.ker_eq_bot_iff.mp (signedPicardHom_ker_eq_bot_of_presentation
    Q P rfl hc M (fun a _ ↦ (hfamily a).1) hD (hfamily c).1 hnef' hsq' hcan hprim' d hmark
      ρ (fun w _ _ _ ↦ (hρ w).2))
  have htarget (w : Word exchangeMatrix exchangeMatrix)
      {C : (Centers).left.PartialMap (Centers).left} [IsDominant C.hom]
      [C.IsOver (Centers).hom (Centers).hom] (R : GeometricRealization M M C (w.xRationalMap ℂ)) :
      ρ eval[w] = R.toSignedBoundaryIsometry d hD hmark := by
    let := Q.complete.nonempty_cones
    let := Q.prestable
    let := Q.neZero
    exact (hρ (End.of w)).2 R (fun a ↦ by
      obtain ⟨p, _⟩ := (Q.hasNodalModel_iff _ _).mp (hfamily (a ≫ C.domainTarget)).1
      exact ⟨p⟩)
  obtain ⟨R, _, _, _⟩ := exists_realize_signed_loop involutionWord P Q rfl hc M
    (fun _ ↦ (hfamily _).1) (hfamily c).1 hD hnef' hsq' hcan hprim' d hmark
  have hgram := (M c).intersectionForm_boundaryClass (hD c) hnef' hsq'
  refine ⟨L, _, H, Q, c, M, hD, hparams, hrays, hfamily, ρ, hinj, ?_, ?_⟩
  · refine eq_centralSign_of_signedRestriction hSymm
      (LinearMap.IsPerfPair.nondegenerate inferInstance) hgram _ ?_ ?_
    · exact (hρ (End.of involutionWord)).1.trans
        ((congrArg (fun n : ℕ ↦ (-1 : ℤˣ) ^ n) inversionCount_involutionWord).trans (pow_one _))
    · rw [htarget involutionWord R]
      exact signedOrthogonalRestriction_of_involution_realization Q hc (fun a ↦ (hfamily a).1)
        c hD d hmark R
  · exact fun w ↦ ⟨(hρ (End.of w)).1, htarget w⟩

/-- The eleven-vertex involution commutes with every independent signed cluster X map. -/
theorem involutionWord_mem_center :
    signedClusterModularGroupMap ℂ exchangeMatrix (End.of involutionWord) ∈ Subgroup.center Γ := by
  obtain ⟨L, _, H, _, c, M, hD, _, _, _, ρ, hinj, hz, _⟩ := exists_eleven_vertex_signedPicardHom 1
  have hcentral := centralSign_mem_center H ((M c).boundaryClass (hD c)) (by decide)
  rw [Subgroup.mem_center_iff]
  intro g
  apply op_injective
  apply hinj
  simpa only [op_mul, map_mul, hz] using (Subgroup.mem_center_iff.mp hcentral (ρ (op g))).symm

end QPainleve.ElevenVertex
