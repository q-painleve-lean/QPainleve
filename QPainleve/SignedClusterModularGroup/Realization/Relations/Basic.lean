/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Boundary

import Mathlib.LinearAlgebra.Matrix.ToLin
import QPainleve.Algebra.Cluster.ChargeKernel.Index
import QPainleve.Algebra.Cluster.Word.CoefficientChange
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness
import QPainleve.SignedClusterModularGroup.Realization.Orthogonal

/-!
# Integer invariants for relations between signed cluster loops

For loops realized in a fixed marked toric presentation, inversion parity, the action on
the charge kernel, and the forward image of component zero determine the X pullback.
The tropical and monomial actions give necessity over any field. For sufficiency,
the marked Picard and ordered boundary actions give equality over ℂ, which specializes
to any field. The kernel action is compared on a finite integral basis, and tropical
evaluation gives the forward index by a finite search among the surviving rays.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative Quiver
open Scheme TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric DiagonalizableGroup
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {l n : ℕ} [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin l)}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Cent" => (Fin l → ℤ)
local notation "T" => Over.mk (structureMap ℂ Cent)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "η[" w "]" => ((-1 : ℤˣ) ^ (Path.inversionCount w))

variable {P : Point (Over.mk (structureMap ℂ (Fin l → ℤ))) →
    MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin l))))}
  (D : ZMod n → L) (hD : ∀ c, D[P c].IsEffectiveCartier)
  (hmark : ∀ c j, (P c).boundaryClass (hD c) j = D j)

local notation "M" => Submodule.span ℤ (Set.range D)
local notation "Orth" => B.orthogonal M
local notation "δ" => ∑ j : ZMod n, D j

variable {C C' : (scheme ℂ (Fin l → ℤ)).PartialMap (scheme ℂ (Fin l → ℤ))}
  [IsDominant C.hom] [IsDominant C'.hom]
  [C.IsOver (Over.mk (structureMap ℂ (Fin l → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin l → ℤ))).hom]
  [C'.IsOver (Over.mk (structureMap ℂ (Fin l → ℤ))).hom
    (Over.mk (structureMap ℂ (Fin l → ℤ))).hom]
  {w v : Word E E}
  (R : GeometricRealization P P C (w.xRationalMap ℂ))
  (R' : GeometricRealization P P C' (v.xRationalMap ℂ))

local notation "sPic" R:arg => (GeometricRealization.toSignedBoundaryIsometry R D hD hmark)
local notation "res[" g "]" => Subtype.val (signedOrthogonalRestriction B D g)

private theorem marked_actions_eq_of_restriction_eq
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (Orth).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hη : R.orientation = R'.orientation)
    (hK : res[sPic R] = res[sPic R'])
    (hj : R.boundaryPerm 0 = R'.boundaryPerm 0) :
    R.picard = R'.picard ∧ R.boundaryPerm = R'.boundaryPerm := by
  have hperm : cycleVertexPerm R.boundaryAction = cycleVertexPerm R'.boundaryAction := by
    apply Equiv.ext
    intro j
    rw [cycleVertexPerm_apply R.boundaryAction j, cycleVertexPerm_apply R'.boundaryAction j,
      ← R.orientation_def,
      ← R'.orientation_def, hη]
    rw [R.boundaryPerm_def, R'.boundaryPerm_def] at hj
    rw [hj]
  have hpic : R.picard = R'.picard := by
    refine boundary_isometry_ext hSymm hsep hspan (fun j ↦ ?_) (fun x hx ↦ ?_)
    · obtain ⟨c⟩ := nonempty_centerPoint (T₀ := T) (T₁ := T) C
      obtain ⟨c'⟩ := nonempty_centerPoint (T₀ := T) (T₁ := T) C'
      have h := R.picard_boundaryClass c (hD _) (hD _) j
      have h' := R'.picard_boundaryClass c' (hD _) (hD _) j
      rw [hmark, hmark, map_inv, hperm] at h
      rw [hmark, hmark, map_inv] at h'
      exact h.trans h'.symm
    · have h := congrArg (fun e : Orth ≃ₗ[ℤ] Orth ↦ (e ⟨x, hx⟩ : L)) hK
      simp only [coe_signedOrthogonalRestriction_apply, SignedBoundaryIsometryGroup.sign_apply,
        toIsometry_apply,
        coe_toSignedBoundaryIsometry, LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm,
        hη] at h
      exact smul_left_cancel R'.orientation h
  exact ⟨hpic, by simpa only [boundaryPerm_def] using hperm⟩

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones] {m : ℕ} [NeZero m]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin l → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {τ : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin l → ℤ)}


local notation "Charge" => LinearMap.ker (Fan.rayChargeMap s)
local notation "Qform" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ Cent))
local notation "χ[" p "]" => pointsEquiv ℂ Cent
  (Subtype.mk (Over.Hom.left (p : Point T)) (Over.w (p : Point T)))
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := T) (Y := T) C
local notation "src[" C "," x "]" =>
  x ≫ PartialMap.domainSource (X := T) (Y := T) C
local notation "fiberAt" c:arg => ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c)
variable
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin l → ℤ))))]

include hmark in
/-- Two signed words with geometric realizations in a fixed ordered toric presentation
have equal X pullbacks over any field exactly when their finite integer invariants agree. The sign
retains the action on the ordered branches, the matrix records exponent transport on
a basis of the charge kernel, and the search returns the forward image of component
zero. Both searches use the boundary order table of one reference fiber, which can
lie outside the centers reached by the two realizations. Nodal contractions at the
reached centers identify their numbered boundary rays with that reference table.
With the basis vectors and order table supplied as integers, `decidable_of_iff`
transfers decidable equality of the computed invariants to equality of the X pullbacks. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq {k : Type*} [Field k]
    [Module.Free ℤ L] [Module.Finite ℤ L] [B.IsPerfPair] (hSymm : B.IsSymm)
    (hGram : ∀ j k, B (D j) (D k) =
      (-2 : ℤ) * (if j = k then 1 else 0) + (if k = j + 1 then 1 else 0) +
        (if k = j - 1 then 1 else 0))
    (hηw : R.orientation = η[w]) (hηv : R'.orientation = η[v])
    (hC : C.hom = C.domain.ι ≫ (w.centerIso ℂ).hom)
    (hC' : C'.hom = C'.domain.ι ≫ (v.centerIso ℂ).hom)
    (hcΦ : Φ.IsComplete)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap s))
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Φ.boundaryIdeal hΦ₀).subscheme.dualGraphVertexEquiv a (τ.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal hΦ₀).subschemeι
        ((Φ.boundaryIdeal hΦ₀).subscheme.dualGraphEdgeEquiv a (τ.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (e : Orth ≃ₗ[ℤ] Charge)
    (he : ∀ x : Charge, ι (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel hΦ s Qform).symm x).val)
    {c₀ : Point T} (p₀ : fiberAt c₀) (hnodal₀ : p₀.IsNodalContraction)
    {U : Set (Point T)}
    (p : ∀ c ∈ U, fiberAt c)
    (hnodal : ∀ c (hc : c ∈ U), (p c hc).IsNodalContraction)
    (hU : ∀ x : CenterPoint (U := T) (V := T) C, src[C,x] ∈ U ∧ dst[C,x] ∈ U)
    (hU' : ∀ x : CenterPoint (U := T) (V := T) C', src[C',x] ∈ U ∧ dst[C',x] ∈ U)
    {d : ℕ} (β : Module.Basis (Fin d) ℤ E.matrix.mulVecLin.ker) :
    let orders := p₀.numberedBoundaryOrders (hD c₀)
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants (fun j ↦ (β j : Cent)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Cent)) orders (orders 0) := by
  dsimp only
  have hne : E.matrix ≠ 0 := hE.symm ▸
    ((Fan.rayChargeMap s).chargeExchangeMatrix_eq_zero_iff_index_range_eq_zero b
      b.detDualEquiv_self b.detDualEquiv_apply_basis_zero_one).not.mpr hindex
  refine ⟨fun h ↦ Path.signedLoopInvariants_eq_of_xPullback_eq hne h β _ _, fun h ↦ ?_⟩
  apply Path.xPullback_eq_of_charZero k ℂ
  have hrays c (hc : c ∈ U) : (p c hc).numberedBoundaryRays (hD c) =
      p₀.numberedBoundaryRays (hD c₀) :=
    (p c hc).numberedBoundaryRays_eq_of_nodalContractions (p₀)
      (hnodal c hc) hnodal₀ (LinearMap.IsPerfPair.separatingRight inferInstance)
  have hkeep c (hc : c ∈ U) ρ := ((p c hc).mem_range_numberedBoundaryRays_iff (hD c) ρ).symm.trans
    (by rw [hrays c hc])
  let Q : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap s, b.detDualEquiv_self, hE.symm⟩
  have hker : E.matrix.mulVecLin.ker = Q.charge.ker := by
    rw [hE]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b s hindex
  have hcharge₁ := chargeKernelAction_eq_signedOrthogonalRestriction u hvertices hdet hnodes
    D hD hmark w R hC Q rfl hker e he hU (fun t ht ↦ (hnodal t ht).genus_zero)
    (fun t ht ↦ ⟨p t ht⟩)
  have hcharge₂ := chargeKernelAction_eq_signedOrthogonalRestriction u hvertices hdet hnodes
    D hD hmark v R' hC' Q rfl hker e he hU' (fun t ht ↦ (hnodal t ht).genus_zero)
    (fun t ht ↦ ⟨p t ht⟩)
  have hmatrix : chargeKernelAction ℂ Q hker eval[w] = chargeKernelAction ℂ Q hker eval[v] ↔
      LinearMap.toMatrixAlgEquiv β w.exchangeKernelEquiv.toLinearMap =
        LinearMap.toMatrixAlgEquiv β v.exchangeKernelEquiv.toLinearMap := by
    simp only [chargeKernelAction_apply, exchangeKernelAction_op_loop,
      (LinearEquiv.autCongr _).injective.eq_iff,
      (LinearMap.toMatrixAlgEquiv β).injective.eq_iff, LinearEquiv.toLinearMap_injective.eq_iff]
  -- Read the geometric boundary permutations from the same integer table.
  obtain ⟨x⟩ := nonempty_centerPoint (T₀ := T) (T₁ := T) C
  obtain ⟨y⟩ := nonempty_centerPoint (T₀ := T) (T₁ := T) C'
  have hsep : (Qform).SeparatingRight := LinearMap.IsPerfPair.separatingRight inferInstance
  have hfind₁ := R.signedLoopInvariants_boundary_eq_some hsep x hcΦ hE hindex p₀ hnodal₀
    (p _ (hU x).1) (p _ (hU x).2) (hnodal _ (hU x).2) (hD _) (fun j ↦ (β j : Cent))
  have hfind₂ := R'.signedLoopInvariants_boundary_eq_some hsep y hcΦ hE hindex p₀ hnodal₀
    (p _ (hU' y).1) (p _ (hU' y).2) (hnodal _ (hU' y).2) (hD _) (fun j ↦ (β j : Cent))
  simp only [Path.signedLoopInvariants_def] at hfind₁ hfind₂
  rw [Path.signedLoopInvariants_eq_iff, ← hmatrix,
    ← (Option.map_injective (ZMod.finEquiv n).toEquiv.injective).eq_iff,
    hfind₁, hfind₂, Option.some.injEq] at h
  obtain ⟨hη, hact, hj⟩ := h
  have hres := congrArg (LinearEquiv.autCongr (LinearEquiv.ofEq Q.charge.ker Charge rfl)) hact
  rw [hcharge₁, hcharge₂] at hres
  have horient := hηw.trans (hη.trans hηv.symm)
  have hB : B.Nondegenerate := LinearMap.IsPerfPair.nondegenerate inferInstance
  obtain ⟨hpic, hperm⟩ := marked_actions_eq_of_restriction_eq D hD hmark R R'
    hSymm hB.1 (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB)
    horient ((LinearEquiv.autCongr e).injective hres) hj
  exact (Path.xRationalMap_eq_iff ℂ w v).mp
    (R.xMap_eq_of_marked_actions_on_center_domains R' hcΦ u hvertices hdet hnodes
      (fun x ↦ p _ (hU x).1) (Set.range (p₀.numberedBoundaryRays (hD c₀)))
      (fun x ↦ ⟨p _ (hU x).2, hnodal _ (hU x).2, hkeep _ (hU x).2⟩)
      (fun x ↦ ⟨p _ (hU' x).2, hnodal _ (hU' x).2, hkeep _ (hU' x).2⟩) hpic hperm horient)

end QPainleve.SignedClusterModularGroup.GeometricRealization
