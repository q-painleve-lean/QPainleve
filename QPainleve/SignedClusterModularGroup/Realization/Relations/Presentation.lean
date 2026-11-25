/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.LoopComparison.List
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary
import QPainleve.SignedClusterModularGroup.Realization.Reflection

/-!
# Deciding relations in a marked toric presentation

A reference nodal contraction determines the boundary orders used to compare signed
loops. The reference center can have repeated blowup centers. The decision procedure
computes an integral kernel basis from the exchange matrix and takes the boundary
orders as integer input. It compares inversion signs, transported basis vectors, and
the results of finite boundary searches.
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
    (w : Word E E) {κ : Type*} (basisVectors : κ → Fin r → ℤ) :
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
        (w.signedLoopInvariants basisVectors orders (orders 0)).boundaryLabel = some j ∧
        ∀ l, (SignedBoundaryIsometryGroup.toIsometry H d
          (R.toSignedBoundaryIsometry d (fun c ↦ cartier(M c)) hmark)).val (d l) =
            d (η • (l - (ZMod.finEquiv n).toEquiv j)) := by
  dsimp only
  have hreference := Q.hasNodalModel_of_contraction hnodal₀
  let : IsRationalOver ((M c₀).surface ↘ S) := hreference.isRationalOver
  let : (M c₀).surface.IsProjectiveOver ℂ := (M c₀).projective
  let : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
  have hcan := congrArg Inv.inv (hreference.canonicalClass (cartier(M c₀)))
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle (M := M) hreference
    (cartier(M c₀)) hnef hsq hcan hprim
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
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
    have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
    rw [← hN, Q.fan.algebraicRealization_over]
    exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular
  let := Q.isPerfPair_auxiliaryPicardForm
  obtain ⟨x⟩ := nonempty_centerPoint (T₀ := Centers[r]) (T₁ := Centers[r]) (w.centerPartialMap ℂ P)
  obtain ⟨hx₀, hx₁⟩ := w.centerPoint_endpoints_mem_noncollision P hker x
  have hfind := R.signedLoopInvariants_boundary_eq_some
    (LinearMap.IsPerfPair.separatingRight inferInstance) x Q.complete hE hindex
    p₀ hnodal₀ (p _ hx₀) (p _ hx₁) (hnodal _ hx₁) (cartier(M _)) basisVectors
  obtain ⟨j, hj, hj₀⟩ := Option.map_eq_some_iff.mp hfind
  refine ⟨R, hη, hmodels, j, hj, fun l ↦ ?_⟩
  rw [hj₀, ← hη]
  simpa only [SignedBoundaryIsometryGroup.toIsometry_apply, coe_toSignedBoundaryIsometry,
    LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm] using
    R.picard_apply_boundaryClass boundaryClasses[M,c₀] (fun c ↦ cartier(M c)) hmark l

/-- The integer comparison decides equality of independent X pullbacks of signed loops
of a primitive nef square-zero cycle. Nodal models are needed on the initial noncollision
open for the realizations. The reference fiber supplying the boundary order table can be
at any center, including a center outside that open. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq_of_presentation
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
    (hnodes : ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
      (Q.rayOrder (j + 1)).toCone ≤ σ ∧
      (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
        ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
          Q.marks (Q.cycle.edge j)).val =
        Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (w v : Word E E)
    {k : ℕ} (β : Basis (Fin k) ℤ E.matrix.mulVecLin.ker) :
    let orders := p₀.numberedBoundaryOrders (cartier(M c₀))
    w.xPullback ℂ = v.xPullback ℂ ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  dsimp only
  -- The reference contraction supplies the lattice and boundary intersection data.
  have hreference := Q.hasNodalModel_of_contraction hnodal₀
  let : IsRationalOver ((M c₀).surface ↘ S) := hreference.isRationalOver
  let : (M c₀).surface.IsProjectiveOver ℂ := (M c₀).projective
  let : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
  let : H.IsPerfPair := (M c₀).isPerfPair_of_isRationalOver
  let : Module.Free ℤ (Additive (LineBundleClass (M c₀).surface)) :=
    (M c₀).surface.free_picard_of_isRationalOver ℂ
  let : Module.Free ℤ L := Module.Free.of_equiv (M c₀).picardMarking.symm
  let : Module.Finite ℤ (Additive (LineBundleClass (M c₀).surface)) :=
    (M c₀).surface.finite_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ L := Module.Finite.of_surjective _ (M c₀).picardMarking.symm.surjective
  have hpair (x y : L) : H x y =
      Chow.classIntersectionNumber ℂ (M c₀).surface ((M c₀).picardMarking x).toMul
        ((M c₀).picardMarking y).toMul :=
    ((M c₀).intersectionBilinForm_picardMarking x y).symm.trans
      (Chow.intersectionBilinForm_apply ..)
  have hSymm : H.IsSymm := ⟨fun x y ↦
    (hpair x y).trans ((Chow.classIntersectionNumber_comm _ _).trans (hpair y x).symm)⟩
  have hcan := congrArg Inv.inv (hreference.canonicalClass (cartier(M c₀)))
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle (M := M) hreference
    (cartier(M c₀)) hnef hsq hcan hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  have models (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :=
    let hx := (Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2
    Q.hasNodalModel_of_contraction (hnodal _ hx)
  -- Realize both words on their noncollision domains.
  have hreal (u : Word E E) := exists_realize_signed_loop u P Q hform hcharge M models
    hreference (fun c ↦ cartier(M c)) hnef hsq hprim boundaryClasses[M,c₀] hmark
  obtain ⟨R, hR, -⟩ := hreal w
  obtain ⟨R', hR', -⟩ := hreal v
  -- Identify the charge coordinates for the common boundary order table.
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let : SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S) := by
    have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
    rw [← hN, Q.fan.algebraicRealization_over]
    exact Q.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Q.regular
  let := Q.isPerfPair_auxiliaryPicardForm
  obtain ⟨e, he, -⟩ := p₀.existsUnique_markedBoundaryOrthogonalEquivChargeKernel
    hnodal₀ (cartier(M c₀)) rfl
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hvertices j := (Q.cycle.component_apply j).symm.trans (Q.component_eq j)
  exact xPullback_eq_iff_signedLoopInvariants_eq boundaryClasses[M,c₀] (fun c ↦ cartier(M c))
    hmark R R' hSymm
    ((M c₀).intersectionForm_boundaryClass (cartier(M c₀)) hnef hsq) hR hR'
    (w.centerPartialMap_hom (K := ℂ) P) (v.centerPartialMap_hom (K := ℂ) P)
    Q.complete hE hindex Q.rayOrder hvertices (fun j ↦ (Q.positive j).1) hnodes
    e he (Q.inclusion_injective hreference) p₀ hnodal₀
    (U := {c : Point Centers[r] | c.left (default : S) ∈ U₀[P]}) p hnodal
    (w.centerPoint_endpoints_mem_noncollision P hker)
    (v.centerPoint_endpoints_mem_noncollision P hker) β

/-- Decide equality of signed loop pullbacks by comparing the three finite invariants.
The kernel basis is computed from the exchange matrix. Supply the boundary orders
as integer data, with their identification supplied by the reference model. -/
def decidableXPullbackEq
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
    (hnodes : ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
      (Q.rayOrder (j + 1)).toCone ≤ σ ∧
      (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
        ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
          Q.marks (Q.cycle.edge j)).val =
        Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (w v : Word E E) (orders : Fin n → Fin r → ℤ)
    (ho : orders = p₀.numberedBoundaryOrders (cartier(M c₀))) :
    Decidable (w.xPullback ℂ = v.xPullback ℂ) :=
  let basisVectors := E.matrix.intKernelBasisVectors.2
  decidable_of_iff
    (w.signedLoopInvariants basisVectors orders (orders 0) =
      v.signedLoopInvariants basisVectors orders (orders 0))
    (by
      obtain ⟨β, hβ⟩ := E.matrix.exists_basis_eq_intKernelBasisVectors
      dsimp only [basisVectors]
      rw [← hβ, ho]
      exact (xPullback_eq_iff_signedLoopInvariants_eq_of_presentation Q P hform hcharge M
        p₀ hnodal₀ p hnodal hnef hsq hprim hmark hnodes w v β).symm)

/-- For the numbered boundary order table of a reference nodal contraction,
a Boolean comparison result certifies that both lists return to the starting
exchange matrix. The result is true exactly when their independent X pullbacks
agree over the given characteristic-zero field. -/
theorem compareSignedLoopLists_eq_some_iff_of_presentation
    (k : Type*) [Field k] [CharZero k]
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
    (hnodes : ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
      (Q.rayOrder (j + 1)).toCone ≤ σ ∧
      (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
        ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
          Q.marks (Q.cycle.edge j)).val =
        Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (orders : Fin n → Fin r → ℤ) (ho : orders = p₀.numberedBoundaryOrders (cartier(M c₀)))
    (gs hs : List (Generator (Fin r))) (result : Bool) :
    E.compareSignedLoopLists orders gs hs = some result ↔
      ∃ w v : Word E E, w.generators = gs ∧ v.generators = hs ∧
        (result = true ↔ w.xPullback k = v.xPullback k) := by
  obtain ⟨β, hβ⟩ := E.matrix.exists_basis_eq_intKernelBasisVectors
  rw [SkewExchangeMatrix.compareSignedLoopLists_eq_some_iff, ← hβ, ho]
  simp_rw [← xPullback_eq_iff_signedLoopInvariants_eq_of_presentation Q P hform hcharge M
    p₀ hnodal₀ p hnodal hnef hsq hprim hmark hnodes _ _ β,
    Path.xPullback_eq_iff_ySeed_coefficient_eq]

end QPainleve.SignedClusterModularGroup.GeometricRealization
