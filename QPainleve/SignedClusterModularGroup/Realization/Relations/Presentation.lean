/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Label
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary
import QPainleve.SignedClusterModularGroup.Realization.Reflection
import QPainleve.SignedClusterModularGroup.Realization.Relations.Boundary

/-!
# Boundary labels of signed loops in a marked toric presentation

A reference nodal contraction supplies the order table for the tropical boundary search.
The label found by the search is the forward image of component zero in the geometric
realization. The reference center can have repeated blowup centers.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open Scheme TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric DiagonalizableGroup
open QPainleve.CharacterTorus QPainleve.Cluster

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}
  {r n : ℕ} [NeZero n] {L γ : Type} [AddCommGroup L]
  {H : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "U₀[" P "]" => Path.centerOpen ℂ Path.nil P

local instance (Q : CompleteToricPresentation i b r L γ) : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance (Q : CompleteToricPresentation i b r L γ) : NeZero Q.length := Q.neZero
local instance (Q : CompleteToricPresentation i b r L γ) :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "pointChar(" c ")" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

local notation "cartier(" M ")" =>
  MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "fiber[" Q "," M "," c "]" =>
  ContractedToricFiber b (CompleteToricPresentation.rays Q) (CompleteToricPresentation.regular Q)
    (CompleteToricPresentation.cycle Q) (CompleteToricPresentation.origin Q)
    (CompleteToricPresentation.inclusion Q) (pointChar(c)) (M c)
local notation "boundaryClasses[" M "," c₀ "]" => MarkedSurface.boundaryClass (M c₀) (cartier(M c₀))

/-- In a marked toric presentation of a primitive nef square-zero anticanonical
cycle, the boundary search succeeds for every signed loop. If it returns the
label `j`, the marked Picard pullback sends `D l` to `D (η • (l - j))`, where
`η` is the inversion sign. The reference contraction supplies the order table,
and the reached models allow this realization to compute the descended Picard action. -/
theorem exists_realize_signed_loop_with_boundary_label
    (Q : CompleteToricPresentation i b r L γ) (P : ChargeSeed E N)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r]) {c₀ : Point Centers[r]}
    (p₀ : fiber[Q,M,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (p : ∀ (c : Point Centers[r]) (_ : c.left (default : S) ∈ U₀[P]), fiber[Q,M,c])
    (hnodal : ∀ c hc, (p c hc).IsNodalContraction)
    (hnef : classOf(cartier(M c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface
      classOf(cartier(M c₀)) classOf(cartier(M c₀)) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier(M c₀))))
    (hmark : ∀ c j, (M c).boundaryClass (cartier(M c)) j = boundaryClasses[M,c₀] j)
    (w : Word E E) :
    let C := w.centerPartialMap ℂ P
    let orders := p₀.numberedBoundaryOrders (cartier(M c₀))
    let d := boundaryClasses[M,c₀]
    let η := (-1 : ℤˣ) ^ w.inversionCount
    ∃ R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) M M C (w.xRationalMap ℂ),
      R.orientation = η ∧
      (∀ x : CenterPoint (U := Centers[r]) (V := Centers[r]) C,
        let c := x ≫ PartialMap.domainTarget (X := Centers[r]) (Y := Centers[r]) C
        Q.HasNodalModel c (M c)) ∧
      ∃ j : Fin n,
        w.tropicalBoundaryLabel orders (orders 0) = some j ∧
        ∀ l, (SignedBoundaryIsometryGroup.toIsometry H d
          (R.toSignedBoundaryIsometry d (fun c ↦ cartier(M c)) hmark)).val (d l) =
            d (η • (l - (ZMod.finEquiv n).toEquiv j)) := by
  dsimp only
  have hreference := Q.hasNodalModel_of_contraction hnodal₀
  let : (M c₀).surface.IsProjectiveOver ℂ := (M c₀).projective
  let : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
  have hindex := hreference.chargeIndex_ne_zero (cartier(M c₀)) hnef hsq hprim
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  have models (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :=
    let hx := (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2
    Q.hasNodalModel_of_contraction (hnodal _ hx)
  obtain ⟨R, hη, -, hmodels⟩ := exists_realize_signed_loop w P Q hform hcharge M models hreference
    (fun c ↦ cartier(M c)) hnef hsq hprim boundaryClasses[M,c₀] hmark
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let := Q.smoothOfRelativeDimension_fan
  let := Q.isPerfPair_auxiliaryPicardForm
  obtain ⟨x⟩ := nonempty_centerPoint (T₀ := Centers[r]) (T₁ := Centers[r]) (w.centerPartialMap ℂ P)
  obtain ⟨hx₀, hx₁⟩ := w.centerPoint_endpoints_mem_noncollision P hker x
  have hfind := R.tropicalBoundaryLabel_eq_some
    (LinearMap.IsPerfPair.separatingRight inferInstance) x Q.complete hE hindex
    p₀ hnodal₀ (p _ hx₀) (p _ hx₁) (hnodal _ hx₁) (cartier(M _))
  refine ⟨R, hη, hmodels, (ZMod.finEquiv n).toEquiv.symm (R.boundaryPerm 0), hfind, fun l ↦ ?_⟩
  rw [Equiv.apply_symm_apply, ← hη]
  simpa only [SignedBoundaryIsometryGroup.toIsometry_apply, coe_toSignedBoundaryIsometry,
    LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm] using
    R.picard_apply_boundaryClass boundaryClasses[M,c₀] (fun c ↦ cartier(M c)) hmark l

end QPainleve.SignedClusterModularGroup.GeometricRealization
