/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction
public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Rationality
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.BranchAction
import TauCeti.LinearAlgebra.Matrix.Dual

/-!
# Faithfulness of the signed Picard action of a toric presentation

On the common noncollision domain, the marked Picard pullback determines the
permutation of boundary components. The sign retains the branch action even
for cycles with one or two components. The marked comparison then recovers
the independent rational X map from these actions. The comparison uses
`ContractedToricFiber.numberedBoundaryRays_eq_of_boundaryClass_eq` to read the
same surviving rays at every reached center.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Multiplicative Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "U₀[" P "]" => Path.centerOpen ℂ Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," c ")" =>
  c ≫ PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin _))) E)
local notation "loopMap" => signedClusterModularGroupMap ℂ

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}

variable (Q : CompleteToricPresentation i b r L γ)

local instance instNonemptyKernelCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroKernelBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableKernelBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

private theorem hasNodalModel_of_contraction
    {M : Point Centers[r] → MarkedSurface ℂ n H XTor[r]} {c : Point Centers[r]}
    (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion (χ[c]) (M c))
    (hp : p.IsNodalContraction) : Q.HasNodalModel c (M c) := by
  obtain ⟨l, Y, W, hW, e, he⟩ := hp.exists_tower
  exact (Q.hasNodalModel_iff c (M c)).mpr ⟨p, Y, l, W, e, hW, he.symm⟩


private theorem smooth_fan :
    SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← hN, Q.fan.algebraicRealization_over]
  exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular

private theorem isPerfPair_of_rational {X : Scheme} (M : MarkedSurface ℂ n H X)
    [IsRationalOver (M.surface ↘ S)] : H.IsPerfPair := by
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ M.surface
  apply LinearMap.IsPerfPair.congr (Chow.intersectionBilinForm ℂ M.surface)
    M.picardMarking M.picardMarking H
  apply LinearMap.ext₂
  intro x y
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
  simpa only [LinearEquiv.apply_symm_apply] using
    (M.intersectionBilinForm_picardMarking (M.picardMarking.symm x)
      (M.picardMarking.symm y)).symm

private theorem rational_fan : IsRationalOver (Q.fan.algebraicRealization ↘ S) := by
  obtain ⟨hdet, σ, h₀, h₁⟩ := Q.positive 0
  have hne : Q.rayOrder 0 ≠ Q.rayOrder (0 + 1) := by
    intro h
    rw [← h, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  exact Q.fan.isRationalOver_of_ray_ne_of_le Q.regular hN hne h₀ h₁

variable [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)]

private theorem separatingRight_aux : (Aux).SeparatingRight := by
  let : IsRationalOver (Q.fan.algebraicRealization ↘ S) := rational_fan Q
  have hperf := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver ℂ Q.fan.algebraicRealization
  refine LinearMap.BilinForm.separatingRight_prod_iff.mpr ⟨hperf.separatingRight, ?_⟩
  intro y hy
  exact (dotProductBilin_isPerfPair ℤ (Fin r)).separatingRight y
    (fun x ↦ by simpa only [LinearMap.neg_apply, neg_eq_zero] using hy x)

local instance instIsDominantKernelLoopXRationalMap (w : Loops[E]) :
    ((End.asHom w).xRationalMap ℂ).IsDominant :=
  Path.instIsDominantXRationalMap ℂ (End.asHom w)

local instance instIsOverKernelLoopXRationalMap (w : Loops[E]) :
    ((End.asHom w).xRationalMap ℂ).IsOver
      (structureMap ℂ (Fin r →₀ ℤ)) (structureMap ℂ (Fin r →₀ ℤ)) :=
  Path.instIsOverXRationalMapStructureMapFinsuppInt ℂ (End.asHom w)

local instance instIsDominantKernelLoopCenterMap (w : Loops[E]) (P : ChargeSeed E N) :
    IsDominant Cw[End.asHom w,P].hom :=
  Path.instIsDominantHomCenterPartialMap (K := ℂ) (End.asHom w) P

local instance instIsOverKernelLoopCenterMap (w : Loops[E]) (P : ChargeSeed E N) :
    Cw[End.asHom w,P].IsOver Centers[r].hom Centers[r].hom :=
  Path.instIsOverCenterPartialMapHomSchemeMkStructureMapForallInt (K := ℂ) (End.asHom w) P

variable {P : ChargeSeed E N} {M : Point (Over.mk (structureMap ℂ (Fin r → ℤ))) →
    MarkedSurface ℂ n H (scheme ℂ (Fin r →₀ ℤ))}
  {U : Set (Point (Over.mk (structureMap ℂ (Fin r → ℤ))))}
  (p : ∀ c ∈ U, ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion (χ[c]) (M c))
  (hnodal : ∀ c hc, (p c hc).IsNodalContraction)
  (hD : ∀ c, D[M c].IsEffectiveCartier)
  (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)

include hnodal hmark in
private theorem xMap_eq_of_signedBoundaryIsometry_eq
    [H.IsPerfPair] (hsep : (Aux).SeparatingRight) (hinj : Function.Injective d)
    (hι : Function.Injective Q.inclusion) {c₀ : Point Centers[r]} (hc₀ : c₀ ∈ U)
    (w v : Loops[E])
    (R : GeometricRealization M M Cw[End.asHom w,P] ((End.asHom w).xRationalMap ℂ))
    (R' : GeometricRealization M M Cw[End.asHom v,P] ((End.asHom v).xRationalMap ℂ))
    (hU : ∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[End.asHom w,P],
      src(Cw[End.asHom w,P],x) ∈ U ∧ dst(Cw[End.asHom w,P],x) ∈ U)
    (hU' : ∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[End.asHom v,P],
      dst(Cw[End.asHom v,P],x) ∈ U)
    (hR : R.toSignedBoundaryIsometry d hD hmark = R'.toSignedBoundaryIsometry d hD hmark) :
    (End.asHom w).xRationalMap ℂ = (End.asHom v).xRationalMap ℂ := by
  have ha := congrArg Subtype.val hR
  simp only [coe_toSignedBoundaryIsometry, Prod.mk.injEq] at ha
  have hpic := H.isometryGroupEquivIsometryEquiv.symm.injective ha.1
  have hp := R.cycleVertexPerm_eq_of_picard_eq R' hmark hmark hinj hpic
  have hrays c (hc : c ∈ U) : (p c hc).numberedBoundaryRays (hD c) =
      (p c₀ hc₀).numberedBoundaryRays (hD c₀) :=
    (p c hc).numberedBoundaryRays_eq_of_boundaryClass_eq (p c₀ hc₀)
      (hnodal c hc) (hnodal c₀ hc₀) hsep (fun j ↦ (hmark c j).trans (hmark c₀ j).symm)
      (by rw [funext (hmark c)]; exact hinj) hι
  have hkeep c (hc : c ∈ U) ρ := ((p c hc).mem_range_numberedBoundaryRays_iff (hD c) ρ).symm.trans
    (by rw [hrays c hc])
  exact R.xMap_eq_of_marked_actions_on_center_domains R' Q.complete Q.rayOrder
    (fun j ↦ (Q.cycle.component_apply j).symm.trans (Q.component_eq j))
    (fun j ↦ (Q.positive j).1)
    (Q.fan.exists_cone_of_numberedBoundaryNode Q.regular Q.complete Q.marks b Q.cycle
      Q.rayOrder Q.component_eq Q.positive)
    (fun x ↦ p _ (hU x).1) (Set.range ((p c₀ hc₀).numberedBoundaryRays (hD c₀)))
    (fun x ↦ ⟨p _ (hU x).2, hnodal _ (hU x).2, hkeep _ (hU x).2⟩)
    (fun x ↦ ⟨p _ (hU' x), hnodal _ (hU' x), hkeep _ (hU' x)⟩) hpic
    (by simpa only [boundaryPerm_def] using hp) ha.2


include hnodal hmark in
private theorem ker_eq_bot_of_realized_actions [H.IsPerfPair]
    (hsep : (Aux).SeparatingRight) (hd : Function.Injective d)
    (hι : Function.Injective Q.inclusion) {c : Point Centers[r]} (hc : c ∈ U)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d)
    (hU : ∀ w : Loops[E], ∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[End.asHom w,P],
      src(Cw[End.asHom w,P],x) ∈ U ∧ dst(Cw[End.asHom w,P],x) ∈ U)
    (hreal : ∀ w : Loops[E],
      ∃ R : GeometricRealization M M Cw[End.asHom w,P] ((End.asHom w).xRationalMap ℂ),
        ρ (op (loopMap E w)) = R.toSignedBoundaryIsometry d hD hmark) :
    ρ.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective ℂ E g.unop
  have hw' : op (loopMap E w) = g := (congrArg op hw).trans (op_unop g)
  obtain ⟨R, hR⟩ := hreal w
  obtain ⟨R', hR'⟩ := hreal 1
  have hactions :
      R.toSignedBoundaryIsometry d hD hmark = R'.toSignedBoundaryIsometry d hD hmark := by
    rw [← hR, hw', MonoidHom.mem_ker.mp hg, ← hR', map_one, op_one, map_one]
  have hx := xMap_eq_of_signedBoundaryIsometry_eq Q p hnodal hD d hmark hsep
    hd hι hc w 1 R R' (hU w) (fun x ↦ (hU 1 x).2) hactions
  have hgroup : loopMap E w = loopMap E 1 :=
    (signedClusterModularGroupMap_eq_iff ℂ E w 1).mpr
      ((Path.xRationalMap_eq_iff ℂ (End.asHom w) (End.asHom (1 : Loops[E]))).mp hx)
  rw [← hw', hgroup, map_one, op_one]

omit [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)] in
/-- The descended signed Picard homomorphism of a fixed marked toric presentation
has trivial kernel. The nodal models of the rational boundary are required on
the initial noncollision open. The reference fiber may lie outside this open.
The sign is part of the recorded action, including when the boundary has one or
two components. -/
theorem signedPicardHom_ker_eq_bot_of_presentation
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (p : ∀ (c : Point Centers[r]) (_ : c.left (default : S) ∈ U₀[P]),
      ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion (χ[c]) (M c))
    (hnodal : ∀ c hc, (p c hc).IsNodalContraction)
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    [IsRationalOver ((M c₀).surface ↘ S)]
    (hnef : classOf(hD c₀).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD c₀) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d)
    (hρ : ∀ (w : Loops[E])
      {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization M M C ((End.asHom w).xRationalMap ℂ)),
      HasToricTargetModels (b := b) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
        (s := Q.rays) (ι := Q.inclusion) (P₁ := M) (fun c : Point Centers[r] ↦ χ[c]) C →
      ρ (op (loopMap E w)) = R.toSignedBoundaryIsometry d hD hmark) :
    ρ.ker = ⊥ := by
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle hmodel (hD c₀) hnef hsq hcan hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  have models (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :=
    let hx := (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2
    hasNodalModel_of_contraction Q (p _ hx) (hnodal _ hx)
  have hd : Function.Injective d := by
    rw [← funext (hmark c₀)]
    exact (M c₀).boundaryClass_injective_of_nef_square_zero (hD c₀) hnef hsq
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := smooth_fan Q
  let : H.IsPerfPair := isPerfPair_of_rational (M c₀)
  obtain ⟨c⟩ := nonempty_centerPoint (T₀ := Centers[r]) (T₁ := Centers[r]) Cnil[P]
  have hc := (Path.nil.centerPoint_endpoints_mem_noncollision P hker c).2
  refine ker_eq_bot_of_realized_actions Q
    (U := {c : Point Centers[r] | c.left (default : S) ∈ U₀[P]})
    p hnodal hD d hmark (separatingRight_aux Q) hd (Q.inclusion_injective hmodel) hc ρ
    (fun w ↦ (End.asHom w).centerPoint_endpoints_mem_noncollision P hker) ?_
  intro w
  obtain ⟨R, -, _, hmodels⟩ := exists_realize_signed_loop (End.asHom w) P Q
    hform hcharge M models hmodel hD hnef hsq hcan hprim d hmark
  exact ⟨R, hρ w R (fun x ↦ ⟨((Q.hasNodalModel_iff _ _).mp (hmodels x)).choose⟩)⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization
