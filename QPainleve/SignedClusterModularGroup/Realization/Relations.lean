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
import QPainleve.Geometry.Toric.Fan.Evaluation.CenterFiber
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness
import QPainleve.SignedClusterModularGroup.Realization.Evaluation

/-!
# Integer invariants for relations between signed cluster loops

For loops realized in a fixed marked toric presentation, inversion parity, the action on
the charge kernel, and the forward image of component zero determine the X pullback.
The proof compares the marked Picard and ordered boundary actions in both directions.
The kernel action is compared using a finite integral basis, and tropical evaluation
gives the forward index by a finite search among the surviving rays.
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
local notation "Xtor" => scheme ℂ (Fin l →₀ ℤ)
local notation "Torus[" U "]" => Grp.X (groupScheme ℂ (FGCommGrpCat.of (Multiplicative U)))
local notation "centerCoordinates" =>
  diagonalizableGroupSchemeIso ℂ (FGCommGrpCat.of (Multiplicative Cent))
local notation "Qform" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ Cent))
local notation "χ[" p "]" => pointsEquiv ℂ Cent
  (Subtype.mk (Over.Hom.left (p : Point T)) (Over.w (p : Point T)))
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := T) (Y := T) C
local notation "orders[" q "," hd "]" => (fun j : Fin n ↦
  Fan.rayBoundaryOrders b s (ContractedToricFiber.numberedBoundaryRays q hd
    (RingEquiv.toEquiv (ZMod.finEquiv n) j)))
local notation "startOrders" => Fan.rayBoundaryOrders b s
  (Equiv.symm (Fan.boundaryNormalizationComponentEquiv Φ hΦ) (τ.component origin))

private theorem xRationalMap_eq_of_marked_actions
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [B.IsPerfPair]
    (hcΦ : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Φ.boundaryIdeal hΦ₀).subscheme.dualGraphVertexEquiv a (τ.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal hΦ₀).subschemeι
        ((Φ.boundaryIdeal hΦ₀).subscheme.dualGraphEdgeEquiv a (τ.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (p : ∀ c : Point T, ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c))
    (hnodal : ∀ c, (p c).IsNodalContraction)
    (survives : Set Φ.Ray) (hkeep : ∀ (c : Point T) (ρ : Φ.Ray),
      (p c).projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
        (fun j ↦ χ[c] (ofAdd (Pi.single j 1))) ρ).val ∈ D[P c].boundaryPrimes ↔ ρ ∈ survives)
    (hpic : R.picard = R'.picard) (hperm : R.boundaryPerm = R'.boundaryPerm)
    (hη : R.orientation = R'.orientation) :
    w.xRationalMap ℂ = v.xRationalMap ℂ := by
  let : Module.Free ℤ N := Module.Free.of_basis b
  let : IsAddFG N := Module.Finite.iff_addGroup_fg.mp (.of_basis b)
  let e := centerCoordinates
  let coord : (Fin l →₀ ℤ) ≃+ Additive (FGCommGrpCat.of (Multiplicative Cent)) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin l)).toAddEquiv
  let eX : Torus[Cent].left ≅ Xtor := e ≪≫ CharacterTorus.mapIso ℂ coord
  have he : e.hom ≫ (T).hom = Torus[Cent].hom := diagonalizableGroupSchemeIso_hom_structureMap ℂ _
  have hcoords : eX.hom = e.hom ≫ CharacterTorus.map ℂ coord.toAddMonoidHom :=
    (Iso.trans_hom e (CharacterTorus.mapIso ℂ coord)).trans
      (congrArg (e.hom ≫ ·) (CharacterTorus.mapIso_hom ℂ coord))
  have heX : eX.hom ≫ structureMap ℂ (Fin l →₀ ℤ) = Torus[Cent].hom := by
    rw [hcoords, Category.assoc, map_structureMap]
    exact he
  let : Nonempty Torus[Cent].left := ⟨e.inv (Classical.choice (inferInstance : Nonempty (T).left))⟩
  let : IsIntegral Torus[Cent].left := IsIntegral.of_isIso e.inv
  let : Smooth Torus[Cent].hom := smooth_groupScheme_of_free ℂ Cent
  let eOver : Torus[Cent] ⟶ T := Over.homMk e.hom he
  let : IsDominant eOver.left := by
    change IsDominant e.hom
    let : IsIso e.hom := Iso.isIso_hom e
    infer_instance
  let : eOver.left.toPartialMap.IsOver Torus[Cent].hom (T).hom := Hom.isOver_toPartialMap he
  let f := eOver.left.toPartialMap
  let : (f.comp C).IsOver Torus[Cent].hom (T).hom :=
    PartialMap.instIsOverCompHom_qPainleve (X := Torus[Cent]) (Y := T) (Z := T) f C
  let : (f.comp C').IsOver Torus[Cent].hom (T).hom :=
    PartialMap.instIsOverCompHom_qPainleve (X := Torus[Cent]) (Y := T) (Z := T) f C'
  let R₀ := (R.precompCenter eOver).precompEvaluation eX
  let R₁ := (R'.precompCenter eOver).precompEvaluation eX
  have hover : eX.hom.toRationalMap.IsOver Torus[Cent].hom (structureMap ℂ (Fin l →₀ ℤ)) := by
    rw [RationalMap.isOver_iff, Hom.toRationalMap_compHom, heX]
  let : (eX.hom.toRationalMap.comp (w.xRationalMap ℂ)).IsOver Torus[Cent].hom
      (structureMap ℂ (Fin l →₀ ℤ)) := RationalMap.isOver_comp _ hover _ inferInstance
  let : (eX.hom.toRationalMap.comp (v.xRationalMap ℂ)).IsOver Torus[Cent].hom
      (structureMap ℂ (Fin l →₀ ℤ)) := RationalMap.isOver_comp _ hover _ inferInstance
  let U := (f.comp C).domain ⊓ (f.comp C').domain
  have hU : Dense (U : Set Torus[Cent].left) :=
    (f.comp C).dense_domain.inter_of_isOpen_left (f.comp C').dense_domain (f.comp C).domain.is_open'
  let : Nonempty U := hU.nonempty.to_subtype
  apply RationalMap.comp_left_injective eX.hom.toRationalMap
  refine R₀.xMap_eq_of_marked_actions_eq R₁
    (by simpa only [R₀, R₁, precompEvaluation_picard, precompCenter_picard] using hpic)
    (by simpa only [R₀, R₁, boundaryPerm_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hperm)
    (by simpa only [R₀, R₁, orientation_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hη)
    (Fan.rayChargeMap s).toAddMonoidHom (structureMap ℂ (Fin l →₀ ℤ)) U inf_le_left inf_le_right
    (fun c _ ↦ ?_) hcΦ u hvertices hdet hnodes (fun c ↦ χ[c]) survives
    (fun x ↦ ⟨p _, hnodal _, hkeep _⟩) (fun y ↦ ⟨p _, hnodal _, hkeep _⟩)
  let c' : (S).asOver S ⟶ Torus[Cent] :=
    Over.homMk c.left ((Over.w c).trans (Spec.map_id (CommRingCat.of ℂ)).symm)
  let χ' := schemePointsMulEquiv (R := ℂ) (A := ℂ) (FGCommGrpCat.of (Multiplicative Cent)) c'
  have hχ : χ' = χ[c ≫ eOver] := by
    apply (pointsEquiv ℂ Cent).symm.injective
    apply Subtype.ext
    rw [Equiv.symm_apply_apply]
    change ((pointsEquiv ℂ Cent).symm χ').val = c'.left ≫ e.hom
    simpa only [χ', MulEquiv.symm_apply_apply, e] using!
      (schemePointsMulEquiv_symm_comp_diagonalizableGroupSchemeIso ℂ (B := Cent) χ').symm
  let q : ContractedToricFiber b s hΦ τ origin ι χ' (P (c ≫ eOver)) :=
    hχ.symm ▸ p (c ≫ eOver)
  obtain ⟨j, hj, hchart⟩ := @Fan.exists_dominant_chart_comp_evaluationAtCenter
    N V _ _ _ i Φ hΦ₀ l b s c.left (Over.w c) hΦ
    (P (c ≫ eOver)).surface (P (c ≫ eOver)).integral q.projection q.modification
  refine ⟨j, hj, ?_⟩
  let ev := evaluationAtCenter ℂ (Fan.rayChargeMap s).toAddMonoidHom c.left (Over.w c)
  have hchart' : j.comp (P (c ≫ eOver)).evaluation = (ev ≫ eX.hom).toRationalMap := by
    rw [q.evaluation_eq, hcoords]
    exact hchart
  change j.comp ((P (c ≫ eOver)).compEvaluation eX.inv).evaluation = ev.toRationalMap
  rw [MarkedSurface.compEvaluation_evaluation, RationalMap.comp_compHom, hchart',
    Hom.toRationalMap_compHom, Category.assoc, eX.hom_inv_id, Category.comp_id]

variable
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
    (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin l → ℤ))))]

include hmark in
/-- Two signed words with geometric realizations in a fixed ordered toric presentation
have equal X pullbacks exactly when their finite integer invariants agree. The sign
retains the action on the ordered branches, the matrix records exponent transport on
a basis of the charge kernel, and the search returns the forward image of component
zero. Each search can read the surviving rays at any center of its realization.
The common nodal contraction data identify the rational X maps from their marked
actions, using the fixed set of surviving rays and the dominant charge charts.
With the basis vectors and order tables supplied as integers, `decidable_of_iff`
transfers decidable equality of the computed invariants to equality of the X pullbacks. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq
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
    (hι : Function.Injective ι)
    (p : ∀ c : Point T, ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c))
    (hnodal : ∀ c, (p c).IsNodalContraction)
    (survives : Set Φ.Ray) (hkeep : ∀ (c : Point T) (ρ : Φ.Ray),
      (p c).projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
        (fun j ↦ χ[c] (ofAdd (Pi.single j 1))) ρ).val ∈ D[P c].boundaryPrimes ↔ ρ ∈ survives)
    (x : CenterPoint (U := T) (V := T) C) (y : CenterPoint (U := T) (V := T) C')
    {d : ℕ} (β : Module.Basis (Fin d) ℤ E.matrix.mulVecLin.ker) :
    w.xPullback ℂ = v.xPullback ℂ ↔
      w.signedLoopInvariants (fun j ↦ (β j : Cent))
          orders[p (dst[C,x]), hD (dst[C,x])] startOrders =
        v.signedLoopInvariants (fun j ↦ (β j : Cent))
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
  have hgenus c := (hnodal c).genus_zero
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
  rw [Path.signedLoopInvariants_eq_iff, ← hmatrix]
  simp only [Fan.boundaryRayOfOrders_eq_find_coordinates, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, ← Fan.rayBoundaryOrders_apply_eq_repr, ← funext_iff]
    at hfind₁ hfind₂
  rw [← (Option.map_injective (ZMod.finEquiv n).toEquiv.injective).eq_iff,
    hfind₁, hfind₂, Option.some.injEq]
  constructor
  · intro h
    have ⟨_, hbranch⟩ := R.marked_actions_eq_of_xMap_eq R'
      ((Path.xRationalMap_eq_iff ℂ w v).mpr h) hcΦ hι hindex (fun c ↦ χ[c])
      (fun c ↦ ⟨p _⟩) (fun c ↦ ⟨p _⟩)
    have hact := (signedClusterModularGroupMap_eq_iff ℂ E (End.of w) (End.of v)).mpr h
    refine ⟨?_, congrArg (fun g ↦ chargeKernelAction ℂ Q hker (op g)) hact, ?_⟩
    · rw [← hηw, ← hηv, R.orientation_def, R'.orientation_def, hbranch]
    · rw [R.boundaryPerm_def, R'.boundaryPerm_def, hbranch]
  · rintro ⟨hη, hact, hj⟩
    have hres := congrArg (LinearEquiv.autCongr (LinearEquiv.ofEq Q.charge.ker Charge rfl)) hact
    rw [hcharge₁, hcharge₂] at hres
    have horient := hηw.trans (hη.trans hηv.symm)
    have hB : B.Nondegenerate := LinearMap.IsPerfPair.nondegenerate inferInstance
    obtain ⟨hpic, hperm⟩ := marked_actions_eq_of_restriction_eq D hD hmark R R'
      hSymm hB.1 (BoundaryCycle.span_sup_orthogonal_rat hGram hSymm hB)
      horient ((LinearEquiv.autCongr e).injective hres) hj
    exact (Path.xRationalMap_eq_iff ℂ w v).mp
      (xRationalMap_eq_of_marked_actions R R' hcΦ u hvertices hdet hnodes p hnodal survives hkeep
        hpic hperm horient)

end QPainleve.SignedClusterModularGroup.GeometricRealization
