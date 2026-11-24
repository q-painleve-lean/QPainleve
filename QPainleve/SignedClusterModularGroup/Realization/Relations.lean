/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.ToLin
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness
import QPainleve.SignedClusterModularGroup.Realization.BranchAction

/-!
# Integer invariants for relations between signed cluster loops

For loops realized in a fixed marked toric presentation, inversion parity, the action on
the charge kernel, and the forward image of component zero determine the X pullback.
The sufficiency argument uses faithfulness of the signed Picard action. The kernel action
is compared using a finite integral basis, and tropical evaluation gives the forward index
by a finite search among the surviving rays.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Multiplicative Quiver
open Scheme TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {l n : ℕ} [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin l)}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A" => (Fin l → ℤ)
local notation "T" => Over.mk (structureMap ℂ A)
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

private theorem signedPicard_eq_of_restriction_eq
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (Orth).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hη : R.orientation = R'.orientation)
    (hK : res[sPic R] = res[sPic R'])
    (hj : R.boundaryPerm 0 = R'.boundaryPerm 0) :
    sPic R = sPic R' := by
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
  apply Subtype.ext
  simp only [coe_toSignedBoundaryIsometry, hpic, hη]

private theorem xPullback_eq_iff_chargeKernelAction_eq
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B D)
    (hρ : Function.Injective ρ)
    (hw : ρ eval[w] = sPic R) (hv : ρ eval[v] = sPic R')
    (hηw : R.orientation = η[w]) (hηv : R'.orientation = η[v])
    (hSymm : B.IsSymm) (hsep : B.SeparatingLeft)
    (hspan : (M).baseChange ℚ ⊔ (Orth).baseChange ℚ =
      (B.baseChange ℚ).orthogonal ((ℤ ∙ δ).baseChange ℚ))
    (hinj : Function.Injective D)
    {N : Type} [AddCommGroup N] (Q : ChargeSeed E N)
    (hker : E.matrix.mulVecLin.ker = Q.charge.ker)
    {H : Type} [AddCommGroup H] (f : Q.charge.ker ≃ₗ[ℤ] H) (e : Orth ≃ₗ[ℤ] H)
    (hKw : LinearEquiv.autCongr f (chargeKernelAction ℂ Q hker eval[w]) =
      LinearEquiv.autCongr e (res[sPic R]))
    (hKv : LinearEquiv.autCongr f (chargeKernelAction ℂ Q hker eval[v]) =
      LinearEquiv.autCongr e (res[sPic R'])) :
    w.xPullback ℂ = v.xPullback ℂ ↔
      η[w] = η[v] ∧ chargeKernelAction ℂ Q hker eval[w] = chargeKernelAction ℂ Q hker eval[v] ∧
        R.boundaryPerm 0 = R'.boundaryPerm 0 := by
  let hmap := signedClusterModularGroupMap_eq_iff ℂ E (End.of w) (End.of v)
  constructor
  · intro h
    have hg : eval[w] = eval[v] := congrArg op (hmap.mpr h)
    have hp := hw.symm.trans ((congrArg ρ hg).trans hv)
    have hh := congrArg Subtype.val hp
    simp only [coe_toSignedBoundaryIsometry, Prod.mk.injEq] at hh
    have he := B.isometryGroupEquivIsometryEquiv.symm.injective hh.1
    have hj := R.cycleVertexPerm_eq_of_picard_eq R' hmark hmark hinj he
    exact ⟨hηw.symm.trans (hh.2.trans hηv), congrArg (chargeKernelAction ℂ Q hker) hg,
      by simpa only [R.boundaryPerm_def, R'.boundaryPerm_def] using Equiv.congr_fun hj 0⟩
  · rintro ⟨hη, hact, hj⟩
    have hres := congrArg (LinearEquiv.autCongr f) hact
    rw [hKw, hKv] at hres
    have hp := signedPicard_eq_of_restriction_eq D hD hmark R R' hSymm hsep hspan
      (hηw.trans (hη.trans hηv.symm)) ((LinearEquiv.autCongr e).injective hres) hj
    exact hmap.mp (op_injective (hρ (hw.trans (hp.trans hv.symm))))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones] {m : ℕ} [NeZero m]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin l → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {τ : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin l → ℤ)}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin l → ℤ))))]

local notation "Charge" => LinearMap.ker (Fan.rayChargeMap s)
local notation "Qform" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ A))
local notation "χ[" p "]" => pointsEquiv ℂ A
  (Subtype.mk (Over.Hom.left (p : Point T)) (Over.w (p : Point T)))
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := T) (Y := T) C
local notation "orders[" q "," hd "]" => (fun j : Fin n ↦
  Fan.rayBoundaryOrders b s (ContractedToricFiber.numberedBoundaryRays q hd
    (RingEquiv.toEquiv (ZMod.finEquiv n) j)))
local notation "startOrders" => Fan.rayBoundaryOrders b s
  (Equiv.symm (Fan.boundaryNormalizationComponentEquiv Φ hΦ) (τ.component origin))

/-- Two signed words with geometric realizations in a fixed ordered toric presentation
have equal X pullbacks exactly when their finite integer invariants agree. The sign
retains the action on the ordered branches, the matrix records exponent transport on
a basis of the charge kernel, and the search returns the forward image of component
zero. Each search can read the surviving rays at any center of its realization.
With the basis vectors and order tables supplied as integers, `decidable_of_iff`
transfers decidable equality of the computed invariants to equality of the X pullbacks. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq
    [Module.Free ℤ L] [Module.Finite ℤ L] (hSymm : B.IsSymm) (hB : B.Nondegenerate)
    (hGram : ∀ j k, B (D j) (D k) =
      (-2 : ℤ) * (if j = k then 1 else 0) + (if k = j + 1 then 1 else 0) +
        (if k = j - 1 then 1 else 0))
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B D)
    (hρ : Function.Injective ρ) (hw : ρ eval[w] = sPic R) (hv : ρ eval[v] = sPic R')
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
    (hgenus : ∀ c : Point T,
      letI := (P c).prestable_boundaryImage
      ∀ z : irreducibleComponents (D[P c].subscheme.singularLocus ℂ).blowup,
        (D[P c].subscheme.blowupComponent (K := ℂ) z).toScheme.genus ℂ = 0)
    (p : ∀ c : Point T, ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c))
    (x : CenterPoint (U := T) (V := T) C) (y : CenterPoint (U := T) (V := T) C')
    {d : ℕ} (β : Module.Basis (Fin d) ℤ E.matrix.mulVecLin.ker) :
    w.xPullback ℂ = v.xPullback ℂ ↔
      w.signedLoopInvariants (fun j ↦ (β j : A))
          orders[p (dst[C,x]), hD (dst[C,x])] startOrders =
        v.signedLoopInvariants (fun j ↦ (β j : A))
          orders[p (dst[C',y]), hD (dst[C',y])] startOrders := by
  let Q : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap s, b.detDualEquiv_self, hE.symm⟩
  let : Module.Free ℤ N := Module.Free.of_basis b
  let : Module.Finite ℤ N := Module.Finite.of_basis b
  let : (Fan.rayChargeMap s).range.toAddSubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_iff.mpr hindex
  have hsep : Q.form.SeparatingRight := by
    intro z hz
    have hz' (t : N) : b.detDualEquiv t z = 0 := hz t
    apply b.detDualEquiv.injective
    rw [map_zero]
    ext t
    simp only [b.detDualEquiv_swap z t, hz' t, neg_zero, LinearMap.zero_apply]
  have hker := Q.exchangeKernel_eq hsep
    (AddSubgroup.finrank_eq_of_finiteIndex (Fan.rayChargeMap s).range.toAddSubgroup)
  have hinj : Function.Injective D := by
    by_cases hn : 2 ≤ n
    · exact BoundaryCycle.injective_of_cycle_gram B D hGram hn
    · have hn' : n = 1 := by
        have := NeZero.ne n
        omega
      subst n
      exact Function.injective_of_subsingleton _
  have hcharge₁ := chargeKernelAction_eq_signedOrthogonalRestriction u hvertices hdet hnodes
    D hD hmark w R hC Q rfl hker e he hgenus (fun c ↦ ⟨p c⟩)
  have hcharge₂ := chargeKernelAction_eq_signedOrthogonalRestriction u hvertices hdet hnodes
    D hD hmark v R' hC' Q rfl hker e he hgenus (fun c ↦ ⟨p c⟩)
  have hmatrix : chargeKernelAction ℂ Q hker eval[w] = chargeKernelAction ℂ Q hker eval[v] ↔
      LinearMap.toMatrixAlgEquiv β w.exchangeKernelEquiv.toLinearMap =
        LinearMap.toMatrixAlgEquiv β v.exchangeKernelEquiv.toLinearMap := by
    simp only [chargeKernelAction_apply, exchangeKernelAction_op_loop,
      (LinearEquiv.autCongr _).injective.eq_iff,
      (LinearMap.toMatrixAlgEquiv β).injective.eq_iff, LinearEquiv.toLinearMap_injective.eq_iff]
  have hfind₁ := R.boundaryRayOfOrders_eq_boundaryPerm x (p _) (p _) (hD _) (hD _) hcΦ hE hindex
  have hfind₂ := R'.boundaryRayOfOrders_eq_boundaryPerm y (p _) (p _) (hD _) (hD _) hcΦ hE hindex
  rw [xPullback_eq_iff_chargeKernelAction_eq D hD hmark R R' ρ hρ hw hv hηw hηv hSymm hB.1
    (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB) hinj Q hker
    (LinearEquiv.ofEq Q.charge.ker Charge rfl) e hcharge₁ hcharge₂,
    Path.signedLoopInvariants_eq_iff, hmatrix]
  simp only [Fan.boundaryRayOfOrders_eq_find_coordinates, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, ← Fan.rayBoundaryOrders_apply_eq_repr, ← funext_iff]
    at hfind₁ hfind₂
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [← Option.some.injEq, ← hfind₁, ← hfind₂, (Option.map_injective
    (ZMod.finEquiv n).toEquiv.injective).eq_iff]

end QPainleve.SignedClusterModularGroup.GeometricRealization
