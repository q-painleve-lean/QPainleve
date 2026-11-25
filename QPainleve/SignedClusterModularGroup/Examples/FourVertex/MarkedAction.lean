/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.PicardAction

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Marking
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Presentation
import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Basic
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary
import QPainleve.SignedClusterModularGroup.Realization.PicardAction
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.PicardAction
import TauCeti.AlgebraicGeometry.Curves.Prestable

/-!
# The geometric Picard action of the four-vertex seed

The ordered octagon blowups give `markedPicardEquiv` on the explicit integral
lattice. Its sign, Casimir action, and pullback of the forward boundary image
are determined by the inversion count, kernel transport, and tropical order
vector of a loop. Its evaluations at the three standard words identify the
generators used in the group normal forms.
-/

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedClusterModularGroup
open QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.FourVertex

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Exponents" => (Fin 4 → ℤ)
local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)
local notation "L" => (Fin 10 → ℤ)
local notation "H" => intersectionForm
local notation "B" => exchangeMatrix
local notation "Orth" =>
  LinearMap.BilinForm.orthogonal H (Submodule.span ℤ (Set.range boundaryClass))
local notation "G" => signedBoundaryIsometryGroup H boundaryClass
local notation "Γ" => (SignedClusterModularGroup ℂ B)ᵐᵒᵖ
local notation "Γ₀" => (ClusterModularGroup ℂ B)ᵐᵒᵖ
local notation "η" => sign H boundaryClass
local notation "act[" g "]" => Subtype.val (signedOrthogonalRestriction H boundaryClass g)
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ B (End.of w))
local notation "trop[" w "]" =>
  Equiv.toFun (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))) w)
local notation "Centers" => Over.mk (structureMap ℂ Exponents)
local notation "XTor" => scheme ℂ (Fin 4 →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "δ" => ∑ j : ZMod 8, boundaryClass j
local notation "eK" => boundaryOrthogonalEquivExchangeKernel

private theorem markedBoundaryNumerics (M : MarkedSurface ℂ 8 H XTor)
    (hD : D[M].IsEffectiveCartier) (hmark : ∀ j, M.boundaryClass hD j = boundaryClass j) :
    IsPrimitive (Additive.ofMul classOf(hD)) ∧ classOf(hD).IsNef ℂ (M.surface ↘ S) ∧
      Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0 := by
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let := (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hδ : M.picardMarking δ = Additive.ofMul classOf(hD) := by
    rw [← funext hmark, M.picardMarking_sum_boundaryClass]
  have horth (j : ZMod 8) : H δ (boundaryClass j) = 0 :=
    (intersectionForm_isSymm.eq _ _).trans
      (Submodule.mem_orthogonalBilin_span.mp sum_boundaryClass_mem_orthogonal
        (Set.mem_range_self j))
  have hpair (x y : L) : Chow.classIntersectionNumber ℂ M.surface
      (M.picardMarking x).toMul (M.picardMarking y).toMul = H x y :=
    (Chow.intersectionBilinForm_apply ℂ M.surface _ _).symm.trans
      (M.intersectionBilinForm_picardMarking x y)
  have hδprim : IsPrimitive (δ : L) :=
    isPrimitive_def.mpr ⟨-(LinearMap.proj (6 : Fin 10)), by decide⟩
  refine ⟨hδ ▸ M.picardMarking.isPrimitive_iff.mpr hδprim, ?_, ?_⟩
  · refine (hD.isNef_inv_mk_toInvertibleSheaf_iff
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (M.surface ↘ S) (n := 2))).mpr ?_
    intro p hp
    obtain ⟨j, rfl⟩ := (M.mem_range_boundaryPrime_iff hD p).mpr hp
    have h := hpair δ (boundaryClass j)
    rw [hδ, ← hmark j, M.picardMarking_boundaryClass, hmark, horth, toMul_ofMul, toMul_ofMul] at h
    exact h.ge
  · rw [← toMul_ofMul (x := classOf(hD)), ← hδ, hpair, map_sum, Finset.sum_eq_zero]
    exact fun j _ ↦ horth j

variable (Q : CompleteToricPresentation i₂ b₂ 4 L Empty)

local instance (Q : CompleteToricPresentation i₂ b₂ 4 L Empty) : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance (Q : CompleteToricPresentation i₂ b₂ 4 L Empty) :
    NeZero (CompleteToricPresentation.length Q) := Q.neZero
local instance (Q : CompleteToricPresentation i₂ b₂ 4 L Empty) :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local instance (Q : CompleteToricPresentation i₂ b₂ 4 L Empty) :
    Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
  Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b₂

local instance (Q : CompleteToricPresentation i₂ b₂ 4 L Empty) :
    SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  rw [Fan.algebraicRealization_over]
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ Exponents))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "fiber[" M "," c "]" => ContractedToricFiber b₂ Q.rays Q.regular Q.cycle
  Q.origin Q.inclusion χ[c] (M c)
local notation "Charge[" q "]" =>
  LinearMap.ker (Fan.rayChargeMap (CompleteToricPresentation.rays q))

private theorem eq_chargeCoordinates [(Aux).IsPerfPair]
    (e : Orth ≃ₗ[ℤ] Charge[Q])
    (he : ∀ x : Charge[Q], Q.inclusion (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays Aux).symm x).val)
    (hcoords : ∀ x : Orth, -(Q.inclusion x.val).2 = (eK x : Exponents))
    (hker : (B).matrix.mulVecLin.ker = Charge[Q]) :
    e = (eK).trans (LinearEquiv.ofEq _ _ hker) := by
  ext x : 1
  apply Subtype.ext
  have h := congrArg Prod.snd (he (e x))
  rw [e.symm_apply_apply, Fan.boundaryOrthogonalEquivChargeKernel_symm_snd] at h
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, ← hcoords, h, neg_neg]

private theorem exchangeKernel_action
    (P : ChargeSeed B (Fin 2 → ℤ)) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (hker : (B).matrix.mulVecLin.ker = P.charge.ker)
    (hker' : (B).matrix.mulVecLin.ker = Charge[Q])
    (g : G) (w : Word B B)
    (h : LinearEquiv.autCongr
        (LinearEquiv.ofEq P.charge.ker Charge[Q] (congrArg LinearMap.ker hcharge))
        (chargeKernelAction ℂ P hker eval[w]) =
      LinearEquiv.autCongr ((eK).trans (LinearEquiv.ofEq _ _ hker')) act[g]) :
    LinearEquiv.autCongr eK act[g] = w.exchangeKernelEquiv := by
  ext x : 1
  apply Subtype.ext
  have hx := congrArg (fun e : Charge[Q] ≃ₗ[ℤ] Charge[Q] ↦ (e
    (LinearEquiv.ofEq _ _ hker' x) : Exponents)) h
  simp only [LinearEquiv.autCongr_apply_apply, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, chargeKernelAction_apply, exchangeKernelAction_op_loop] at hx
  simpa only [LinearEquiv.autCongr_apply_apply, LinearEquiv.coe_ofEq_apply, LinearEquiv.ofEq_symm,
    Path.coe_exchangeKernelEquiv_apply] using hx.symm

private theorem boundary_pullback
    (M : Point Centers → MarkedSurface ℂ 8 H XTor) (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hmark : ∀ c j, (M c).boundaryClass (hD c) j = boundaryClass j)
    (p : ∀ c, fiber[M,c])
    (horders : ∀ c (j : Fin 8), Fan.rayBoundaryOrders b₂ Q.rays
      ((p c).numberedBoundaryRays (hD c) (ZMod.finEquiv 8 j)) = boundaryOrders j)
    {P : ChargeSeed B (Fin 2 → ℤ)}
    (hE : (B).matrix = chargeExchangeMatrix (b₂).detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (w : Word B B)
    (R : GeometricRealization M M (Path.centerPartialMap ℂ w P) (w.xRationalMap ℂ))
    (hR : R.picard (boundaryClass (R.boundaryPerm 0)) = boundaryClass 0) :
    ∃ j : Fin 8, boundaryOrders j = trop[w] (boundaryOrders 0) ∧
      (toIsometry H boundaryClass (R.toSignedBoundaryIsometry boundaryClass hD hmark)).val
        (boundaryClass (ZMod.finEquiv 8 j)) = boundaryClass 0 := by
  obtain ⟨x⟩ := nonempty_centerPoint (T₀ := Centers) (T₁ := Centers) (Path.centerPartialMap ℂ w P)
  let c₀ := x ≫ (Path.centerPartialMap ℂ w P).domainSource (X := Centers) (Y := Centers)
  let c₁ := x ≫ (Path.centerPartialMap ℂ w P).domainTarget (X := Centers) (Y := Centers)
  let j : Fin 8 := (ZMod.finEquiv 8).symm (R.boundaryPerm 0)
  have hj : ZMod.finEquiv 8 j = R.boundaryPerm 0 := (ZMod.finEquiv 8).apply_symm_apply _
  have hz : ZMod.finEquiv 8 0 = 0 := (ZMod.finEquiv 8).map_zero
  have h := (R.fiber x).rayBoundaryOrders_tropical (p := p c₀) (q := p c₁)
    (hD c₀) (hD c₁) Q.complete hE 0
  rw [← R.boundaryPerm_def, ← hj, horders, ← hz, horders] at h
  refine ⟨j, h, ?_⟩
  simpa only [hj, toIsometry_apply, coe_toSignedBoundaryIsometry,
    LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm] using hR

private theorem exists_markedPicardEquiv :
    ∃ ρ : Γ ≃* G,
      ((η).comp ρ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ B).range ∧
      ∀ w : Word B B, η (ρ eval[w]) = (-1 : ℤˣ) ^ w.inversionCount ∧
        LinearEquiv.autCongr eK act[ρ eval[w]] = w.exchangeKernelEquiv ∧
        ∃ j : Fin 8, boundaryOrders j = trop[w] (boundaryOrders 0) ∧
          (toIsometry H boundaryClass (ρ eval[w])).val (boundaryClass (ZMod.finEquiv 8 j)) =
            boundaryClass 0 := by
  -- Mark the octagon in the lattice with two ruling classes and eight exceptional classes.
  obtain ⟨_, _, _, _, _, Φ, hΦ, hc, v, _, _, _, _, _, _, _, hv, hnext, _⟩ :=
    exists_four_vertex_octagon_blowup
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [Fan.algebraicRealization_over]
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let I := picardCoordinateIsometry hΦ v hv hc hnext
  obtain ⟨Q, P, M, hD, _, _, _, _, hι, hform, hcharge, hindex, horders, hnodes, hfiber⟩ :=
    exists_four_vertex_marked_presentation hΦ hc v hv hnext I
  have hmark c j : (M c).boundaryClass (hD c) j = boundaryClass j := by
    rw [(hfiber c).2.2 j, ← picardCoordinateIsometry_boundaryClass hΦ v hv hc hnext,
      LinearMap.BilinForm.IsometryEquiv.symm_apply_apply]
  have hcoords (x : Orth) : -(Q.inclusion x.val).2 = (eK x : Exponents) := by
    rw [hι, boundaryOrthogonalEquivExchangeKernel_apply]
    exact neg_snd_picardCoordinateIsometry hΦ v hv hc hnext x
  choose p hnodal hrays using fun c ↦ (hfiber c).2.1
  have horders' (c : Point Centers) (j : Fin 8) : Fan.rayBoundaryOrders b₂ Q.rays
      ((p c).numberedBoundaryRays (hD c) (ZMod.finEquiv 8 j)) = boundaryOrders j :=
    (congrArg (Fan.rayBoundaryOrders b₂ Q.rays) (hrays c j)).trans (horders j)
  let c₀ : Point Centers := centerPoint (fun _ ↦ 1)
  have hmodel := (hfiber c₀).1
  let : IsRationalOver ((M c₀).surface ↘ S) := hmodel.isRationalOver
  obtain ⟨hprim, hnef, hsq⟩ := markedBoundaryNumerics (M c₀) (hD c₀) (hmark c₀)
  obtain ⟨ρ, hρ, -⟩ := existsUnique_signedPicardEquiv_of_presentation (Q := Q)
    (hmark := hmark) P hform hcharge (fun c _ ↦ (hfiber c).1) hmodel hprim hnef hsq
  refine ⟨ρ, hρ.sign_ker_unop, fun w ↦ ?_⟩
  -- Compare the kernel transport and boundary orders on the same realization.
  let := Q.isPerfPair_auxiliaryPicardForm
  let : (H).IsPerfPair := (M c₀).isPerfPair_of_isRationalOver
  obtain ⟨e, he, -⟩ := (p c₀).existsUnique_markedBoundaryOrthogonalEquivChargeKernel
    (hnodal c₀) (hD c₀) (funext (hmark c₀))
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hker' : (B).matrix.mulVecLin.ker = Charge[Q] := by
    rw [hE]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b₂ Q.rays (by rw [hindex]; decide)
  have hker : (B).matrix.mulVecLin.ker = P.charge.ker :=
    hker'.trans (congrArg LinearMap.ker hcharge).symm
  obtain ⟨R, _, hR₀, _⟩ := exists_realize_signed_loop w P Q
    hform hcharge M (fun x ↦ (hfiber _).1) hmodel hD hnef hsq hprim boundaryClass hmark
  have hR : ρ eval[w] = R.toSignedBoundaryIsometry boundaryClass hD hmark :=
    hρ.apply_of_realization w R (fun x ↦ ⟨p _⟩)
  refine ⟨hρ.sign_apply_word w, ?_, ?_⟩
  · have h := chargeKernelAction_eq_signedOrthogonalRestriction Q.rayOrder
      (fun j ↦ (Q.cycle.component_apply j).symm.trans (Q.component_eq j))
      (fun j ↦ (Q.positive j).1) hnodes boundaryClass hD hmark w R
      (w.centerPartialMap_hom (K := ℂ) P) P hcharge hker e he
      (U := Set.univ) (fun _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩)
      (fun c _ ↦ (hnodal c).genus_zero) (fun c _ ↦ ⟨p c⟩)
    rw [← hR, eq_chargeCoordinates Q e he hcoords hker'] at h
    exact exchangeKernel_action Q P hcharge hker hker' (ρ eval[w]) w h
  · rw [hR]
    exact boundary_pullback Q M hD hmark p horders' hE w R hR₀

public section

/-- The opposite signed cluster modular group of the doubled-square seed is the
signed boundary isometry group of its marked octagon. -/
noncomputable def markedPicardEquiv : Γ ≃* G :=
  exists_markedPicardEquiv.choose

/-- In point-map order, the sign kernel of the marked Picard action is the unsigned subgroup. -/
theorem ker_sign_comp_markedPicardEquiv :
    ((η).comp markedPicardEquiv.toMonoidHom).ker.unop =
      (clusterModularGroupInclusion ℂ B).range :=
  exists_markedPicardEquiv.choose_spec.1

/-- The sign of a loop's marked Picard action is its inversion parity. -/
@[simp]
theorem sign_markedPicardEquiv_loop (w : Word B B) :
    (markedPicardEquiv eval[w]).val.2 = (-1 : ℤˣ) ^ w.inversionCount := by
  rw [← SignedBoundaryIsometryGroup.sign_apply H boundaryClass]
  exact (exists_markedPicardEquiv.choose_spec.2 w).1

/-- In exchange-kernel coordinates the signed orthogonal Picard action is loop transport. -/
@[simp]
theorem signedOrthogonalRestriction_markedPicardEquiv_loop (w : Word B B) :
    LinearEquiv.autCongr eK act[markedPicardEquiv eval[w]] = w.exchangeKernelEquiv :=
  (exists_markedPicardEquiv.choose_spec.2 w).2.1

/-- Tropical transport from boundary component zero finds the class that the marked
Picard action pulls back to component zero. -/
theorem exists_boundary_pullback_markedPicardEquiv_loop (w : Word B B) :
    ∃ j : Fin 8, boundaryOrders j = trop[w] (boundaryOrders 0) ∧
      (toIsometry H boundaryClass (markedPicardEquiv eval[w])).val
        (boundaryClass (ZMod.finEquiv 8 j)) = boundaryClass 0 :=
  (exists_markedPicardEquiv.choose_spec.2 w).2.2

/-- The marked Picard action of an unsigned cluster map has positive sign. -/
@[simp]
theorem sign_markedPicardEquiv_inclusion (g : Γ₀) :
    (markedPicardEquiv (op (clusterModularGroupInclusion ℂ B g.unop))).val.2 = 1 := by
  have h := congrArg (fun p : G ↦ p.val.2) (rotationInclusion_picardRotationEquiv_apply
    markedPicardEquiv ker_sign_comp_markedPicardEquiv g)
  simpa only [MonoidHom.op_apply_apply, Function.comp_apply, coe_rotationInclusion] using h.symm

/-- The marked Picard action has the same sign, Casimir columns and forward
boundary label as the loop. -/
@[simp]
theorem picardInvariants_markedPicardEquiv_loop (w : Word B B) :
    picardInvariants (markedPicardEquiv eval[w]) =
      w.signedLoopInvariants (fun j ↦ (exchangeKernelBasis j : Fin 4 → ℤ))
        boundaryOrders (boundaryOrders 0) := by
  obtain ⟨j, htrop, hpullback⟩ := exists_boundary_pullback_markedPicardEquiv_loop w
  refine (picardInvariants_eq_signedLoopInvariants_iff _ w).mpr
    ⟨?_, signedOrthogonalRestriction_markedPicardEquiv_loop w, j, hpullback, htrop.symm⟩
  rw [SignedBoundaryIsometryGroup.sign_apply]
  exact sign_markedPicardEquiv_loop w

/-- The rotation word acts by the marked octagon's quarter-turn pullback. -/
@[simp]
theorem markedPicardEquiv_rotationWord :
    markedPicardEquiv eval[rotationWord] = rotationInclusion H boundaryClass quarterTurn :=
  (picardInvariants_eq_rotationWord_iff _).mp (picardInvariants_markedPicardEquiv_loop _)

/-- The translation word acts by the marked Picard translation. -/
@[simp]
theorem markedPicardEquiv_translationWord :
    markedPicardEquiv eval[translationWord] = rotationInclusion H boundaryClass picardTranslation :=
  (picardInvariants_eq_translationWord_iff _).mp (picardInvariants_markedPicardEquiv_loop _)

/-- The signed reflection word acts by the marked boundary reflection. -/
@[simp]
theorem markedPicardEquiv_reflectionWord :
    markedPicardEquiv eval[reflectionWord] = boundaryReflection :=
  (picardInvariants_eq_reflectionWord_iff _).mp (picardInvariants_markedPicardEquiv_loop _)

end

end QPainleve.FourVertex
