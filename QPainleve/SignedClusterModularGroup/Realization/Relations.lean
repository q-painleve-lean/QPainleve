/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.ChargeKernel
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization
public import QPainleve.SignedClusterModularGroup.Realization.NumberedRays

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
local notation "src[" C "," x "]" =>
  x ≫ PartialMap.domainSource (X := T) (Y := T) C
local notation "fiberAt" c:arg => ContractedToricFiber b s hΦ τ origin ι (χ[c]) (P c)
private abbrev HasFiberWithRays (c : Point T) (R : Set Φ.Ray) : Prop :=
  ∃ p : fiberAt c, p.IsNodalContraction ∧ ∀ ρ : Φ.Ray,
    p.projection (Fan.internalBlowupBoundaryPrimeEquiv hΦ b s
      (fun j ↦ χ[c] (ofAdd (Pi.single j 1))) ρ).val ∈ D[P c].boundaryPrimes ↔ ρ ∈ R
local notation "fiberWithRays" c:arg "in" S₀:arg =>
  HasFiberWithRays (P := P) (b := b) (s := s) (hΦ := hΦ) (τ := τ) (origin := origin) (ι := ι) c S₀
local notation "orders[" q "," hd "]" => (fun j : Fin n ↦
  Fan.rayBoundaryOrders b s (ContractedToricFiber.numberedBoundaryRays q hd
    (RingEquiv.toEquiv (ZMod.finEquiv n) j)))
local notation "startOrders" => Fan.rayBoundaryOrders b s
  (Equiv.symm (Fan.boundaryNormalizationComponentEquiv Φ hΦ) (τ.component origin))

omit [IsDominant C.hom] in
private theorem precompCenter_target
    {A : Over S} [PreirreducibleSpace A.left]
    (f : A.left.PartialMap (T).left) [IsDominant f.hom]
    [f.IsOver A.hom (T).hom] [(f.comp C).IsOver A.hom (T).hom]
    (G : Point T → Prop)
    (hG : ∀ x : CenterPoint (U := T) (V := T) C, G (dst[C,x]))
    (x : CenterPoint (U := A) (V := T) (f.comp C)) :
    G (x ≫ PartialMap.domainTarget (X := A) (Y := T) (f.comp C)) := by
  have hx := hG (x ≫ f.compDomainRight (Z := T) C)
  rw [Category.assoc, f.compDomainRight_target] at hx
  exact hx

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
    (pSource : ∀ x : CenterPoint (U := T) (V := T) C, fiberAt (src[C,x]))
    (survives : Set Φ.Ray)
    (pTarget : ∀ x : CenterPoint (U := T) (V := T) C, fiberWithRays (dst[C,x]) in survives)
    (qTarget : ∀ x : CenterPoint (U := T) (V := T) C', fiberWithRays (dst[C',x]) in survives)
    (hpic : R.picard = R'.picard) (hperm : R.boundaryPerm = R'.boundaryPerm)
    (hη : R.orientation = R'.orientation) :
    w.xRationalMap ℂ = v.xRationalMap ℂ := by
  -- The comparison uses the group-scheme coordinates for the joint evaluation map.
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
  refine R₀.xMap_eq_of_marked_actions_eq (s := s) (origin := origin) (ι := ι) R₁
    (by simpa only [R₀, R₁, precompEvaluation_picard, precompCenter_picard] using hpic)
    (by simpa only [R₀, R₁, boundaryPerm_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hperm)
    (by simpa only [R₀, R₁, orientation_def, precompEvaluation_boundaryAction,
      precompCenter_boundaryAction] using hη)
    (Fan.rayChargeMap s).toAddMonoidHom (structureMap ℂ (Fin l →₀ ℤ)) U inf_le_left inf_le_right
    ?_ hcΦ u hvertices hdet hnodes (fun c ↦ χ[c]) survives
    (precompCenter_target (C := C) f (fun c ↦ fiberWithRays c in survives) pTarget)
    (precompCenter_target (C := C') f (fun c ↦ fiberWithRays c in survives) qTarget)
  rintro c ⟨z, hz⟩
  -- A section of the common domain gives a source fiber of the first realization.
  have hleft : (z ≫ Scheme.homOfLE _ (inf_le_left : U ≤ (f.comp C).domain)) ≫
      (f.comp C).domain.ι = c.left := by
    rwa [Category.assoc, Scheme.homOfLE_ι]
  let t : CenterPoint (U := Torus[Cent]) (V := T) (f.comp C) :=
    Over.homMk (z ≫ Scheme.homOfLE _ (inf_le_left : U ≤ (f.comp C).domain))
      (by exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hleft).trans (Over.w c)))
  let x := t ≫ f.compDomainRight (Z := T) C
  have hx : src[C,x] = c ≫ eOver := by
    have ht : t ≫ PartialMap.domainSource (X := Torus[Cent]) (Y := T) (f.comp C) = c := by
      apply Over.OverMorphism.ext
      simpa only [t, Over.comp_left, Over.homMk_left, PartialMap.domainSource_left] using hleft
    have hf : f.domainTarget = f.domainSource ≫ eOver :=
      PartialMap.domainTarget_toPartialMap eOver rfl
    rw [Category.assoc, ← f.compDomainLeft_target (Z := T) C, hf,
      ← Category.assoc (f.compDomainLeft (Z := T) C), f.compDomainLeft_source (Z := T),
      ← Category.assoc, ht]
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
    hχ.symm ▸ hx ▸ pSource x
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
zero. Both searches use the boundary order table of one reference fiber. The
nodal models need only be available at the centers reached by the two realizations.
With the basis vectors and order table supplied as integers, `decidable_of_iff`
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
    {U : Set (Point T)} {c₀ : Point T} (hc₀ : c₀ ∈ U)
    (p : ∀ c ∈ U, fiberAt c)
    (hnodal : ∀ c (hc : c ∈ U), (p c hc).IsNodalContraction)
    (hU : ∀ x : CenterPoint (U := T) (V := T) C, src[C,x] ∈ U ∧ dst[C,x] ∈ U)
    (hU' : ∀ x : CenterPoint (U := T) (V := T) C', src[C',x] ∈ U ∧ dst[C',x] ∈ U)
    {d : ℕ} (β : Module.Basis (Fin d) ℤ E.matrix.mulVecLin.ker) :
    w.xPullback ℂ = v.xPullback ℂ ↔
      w.signedLoopInvariants (fun j ↦ (β j : Cent))
          orders[p c₀ hc₀, hD c₀] startOrders =
        v.signedLoopInvariants (fun j ↦ (β j : Cent))
          orders[p c₀ hc₀, hD c₀] startOrders := by
  -- Use the marked classes to transport every target's numbering to the reference fiber.
  have hinj : Function.Injective D := by
    by_cases hn : 2 ≤ n
    · exact BoundaryCycle.injective_of_cycle_gram B D hGram hn
    · have hn' : n = 1 := by have := NeZero.ne n; omega
      subst n
      exact Function.injective_of_subsingleton _
  have hrays c (hc : c ∈ U) : (p c hc).numberedBoundaryRays (hD c) =
      (p c₀ hc₀).numberedBoundaryRays (hD c₀) :=
    (p c hc).numberedBoundaryRays_eq_of_boundaryClass_eq (p c₀ hc₀)
      (hnodal c hc) (hnodal c₀ hc₀) (LinearMap.IsPerfPair.separatingRight inferInstance)
      (fun j ↦ (hmark c j).trans (hmark c₀ j).symm)
      (fun i j hij ↦ hinj ((hmark c i).symm.trans (hij.trans (hmark c j)))) hι
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
  have hfind₁ := R.boundaryRayOfOrders_eq_boundaryPerm x (p _ (hU x).1) (p _ (hU x).2)
    (hD _) (hD _) hcΦ hE hindex
  have hfind₂ := R'.boundaryRayOfOrders_eq_boundaryPerm y (p _ (hU' y).1) (p _ (hU' y).2)
    (hD _) (hD _) hcΦ hE hindex
  rw [hrays _ (hU x).2] at hfind₁
  rw [hrays _ (hU' y).2] at hfind₂
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
      (fun c ↦ ⟨p _ (hU c).2⟩) (fun c ↦ ⟨p _ (hU' c).2⟩)
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
      (xRationalMap_eq_of_marked_actions R R' hcΦ u hvertices hdet hnodes
        (fun x ↦ p _ (hU x).1) (Set.range ((p c₀ hc₀).numberedBoundaryRays (hD c₀)))
        (fun x ↦ ⟨p _ (hU x).2, hnodal _ (hU x).2, hkeep _ (hU x).2⟩)
        (fun x ↦ ⟨p _ (hU' x).2, hnodal _ (hU' x).2, hkeep _ (hU' x).2⟩) hpic hperm horient)

end QPainleve.SignedClusterModularGroup.GeometricRealization

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N}
  {r n : ℕ} [NeZero n] {L γ : Type} [AddCommGroup L]
  {H : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "U₀[" P "]" => Path.centerOpen ℂ Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," c ")" =>
  c ≫ PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C

private theorem centerPoint_endpoints_mem_noncollision (w : Word E E) (P : ChargeSeed E N)
    (hker : E.matrix.mulVecLin.ker = P.charge.ker)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P]) :
    (src(Cw[w,P],x)).left (default : S) ∈ U₀[P] ∧
      (dst(Cw[w,P],x)).left (default : S) ∈ U₀[P] := by
  constructor
  · rw [Over.comp_left, PartialMap.domainSource_left, Scheme.Hom.comp_apply]
    apply w.centerOpen_le_centerOpen_nil ℂ P
    rw [← w.centerPartialMap_domain (K := ℂ) P]
    exact (x.left (default : S)).property
  · rw [Over.comp_left, PartialMap.domainTarget_left, Scheme.Hom.comp_apply]
    apply w.centerPartialMap_opensRange_le_centerOpen_nil P hker
    exact (Cw[w,P]).hom.mem_opensRange.mpr (Set.mem_range_self _)

variable (Q : CompleteToricPresentation i b r L γ)
local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "pointChar(" c ")" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)]
variable [LinearMap.IsPerfPair (LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]
  [Module.Free ℤ L] [Module.Finite ℤ L] [H.IsPerfPair]

/-- Two signed loops in an ordered presentation of a primitive nef square-zero
anticanonical cycle have the same independent X pullback exactly when their
integer invariants agree. A reference fiber supplies the order table for both
words. The comparison includes one- and two-component boundaries and uses the
models on the initial noncollision open. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq_of_presentation
    (w v : Word E E) (P : ChargeSeed E N)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {c₀ : Point Centers[r]} (hc₀ : c₀.left (default : S) ∈ U₀[P])
    (p : ∀ (c : Point Centers[r]) (_ : c.left (default : S) ∈ U₀[P]),
      ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion (pointChar(c)) (M c))
    (hnodal : ∀ c hc, (p c hc).IsNodalContraction)
    [IsRationalOver ((M c₀).surface ↘ S)]
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD c₀) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
    (hSymm : H.IsSymm)
    (hGram : ∀ j k, H (d j) (d k) = (-2 : ℤ) * (if j = k then 1 else 0) +
      (if k = j + 1 then 1 else 0) + (if k = j - 1 then 1 else 0))
    (hnodes : ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
      (Q.rayOrder (j + 1)).toCone ≤ σ ∧
      (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
        ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
          Q.marks (Q.cycle.edge j)).val =
        Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0)
    (hι : Function.Injective Q.inclusion)
    (e : H.orthogonal (Submodule.span ℤ (Set.range d)) ≃ₗ[ℤ] (Fan.rayChargeMap Q.rays).ker)
    (he : ∀ x, Q.inclusion (e.symm x).val =
      ((Fan.boundaryOrthogonalEquivChargeKernel Q.regular Q.rays
        ((Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization).prod
          (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))).symm x).val)
    {k : ℕ} (β : Module.Basis (Fin k) ℤ E.matrix.mulVecLin.ker) :
    w.xPullback ℂ = v.xPullback ℂ ↔
      let orders (j : Fin n) := Fan.rayBoundaryOrders b Q.rays
        ((p c₀ hc₀).numberedBoundaryRays (hD c₀) ((ZMod.finEquiv n).toEquiv j))
      let start := Fan.rayBoundaryOrders b Q.rays (Q.rayOrder Q.origin)
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders start =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders start := by
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [← P.matrix_eq, hform, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  have hmodel (c : Point Centers[r]) (hc : c.left (default : S) ∈ U₀[P]) :
      Q.HasNodalModel c (M c) := by
    obtain ⟨l, Y, A, hA, f, hf⟩ := (hnodal c hc).exists_tower
    exact (Q.hasNodalModel_iff c (M c)).mpr ⟨p c hc, Y, l, A, f, hA, hf.symm⟩
  have models (x : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P]) :=
    hmodel _ (centerPoint_endpoints_mem_noncollision Path.nil P hker x).2
  obtain ⟨R, hR, -⟩ := exists_realize_signed_loop w P Q hform hcharge M models
    (hmodel c₀ hc₀) hD hnef hsq hcan hprim d hmark
  obtain ⟨R', hR', -⟩ := exists_realize_signed_loop v P Q hform hcharge M models
    (hmodel c₀ hc₀) hD hnef hsq hcan hprim d hmark
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hvertices j := (Q.cycle.component_apply j).symm.trans (Q.component_eq j)
  have hstart := Q.component_eq Q.origin
  have horigin := (Q.fan.boundaryNormalizationComponentEquiv Q.regular).symm_apply_eq.mpr hstart
  simpa only [horigin] using
    xPullback_eq_iff_signedLoopInvariants_eq d hD hmark R R' hSymm hGram hR hR'
      (w.centerPartialMap_hom (K := ℂ) P) (v.centerPartialMap_hom (K := ℂ) P)
      Q.complete hE hindex Q.rayOrder hvertices (fun j ↦ (Q.positive j).1) hnodes
      e he hι (U := {c : Point Centers[r] | c.left (default : S) ∈ U₀[P]}) hc₀ p hnodal
      (centerPoint_endpoints_mem_noncollision w P hker)
      (centerPoint_endpoints_mem_noncollision v P hker) β

end QPainleve.SignedClusterModularGroup.GeometricRealization
