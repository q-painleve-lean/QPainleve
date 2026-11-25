/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Comparison
public import QPainleve.Geometry.Toric.Fan.TorusAction.Orientation.Basic

import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint

/-!
# Marked actions determined by a rational X map

At a common source center, two realizations of the same X map have a residual isomorphism
between their target fibers. For targets from the same ordered toric presentation with
finite-index charges, its lift is a torus translation. Consequently the two realizations
have the same Picard pullback and the same action on the ordered boundary branches.
The translating lift is supplied by
`Fan.existsUnique_translation_of_comp_contractedXEvaluation_eq`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open TauCeti QPainleve.BlowupTower TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open MarkedSurface (surfaceIso boundaryIso)

section ContractedToric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L₀ L₁ : Type}
  [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "center" c:arg => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "Model[" b "," s "," c "]" => Fan.internalBlowupTower b s (center c)
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)

variable [toricPrestable : PrestableFamily (Dtor[Φ,h₀] ↘ S)]
  {γ : Type*} {a : γ → (Dtor[Φ,h₀] ↘ S).smoothLocus}
  (T : Scheme.NodalCycleNumbering a m) (origin : ZMod m) (ι : L₁ →ₗ[ℤ] Pic[Φ,r])

/-- The projections from an ordered toric model associated to a marked surface at a given
center. The class inclusion and the marked initial component are fixed in the auxiliary
toric coordinates. The conductor subdivision records the orientation of the actual
boundary branches. -/
@[ext]
structure ContractedToricFiber (c : Multiplicative (Fin r → ℤ) →* ℂˣ)
    (P : MarkedSurface ℂ n B₁ Xtor[r]) where
  /-- The contraction from the ordered internal blowup model. -/
  projection : (Model[b,s,c]).1 ⟶ P.surface
  /-- The projection is a modification. -/
  [modification : IsModification projection]
  /-- The two projections from the ordered model are over the same field. -/
  projection_over :
    projection ≫ (P.surface ↘ S) =
      (Model[b,s,c]).2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap
  /-- The inverse image of the boundary has the support of the strict toric boundary. -/
  support_comap :
    (P.pair.hom.left.ker.comap projection).support = (Model[b,s,c]).2.boundaryι.ker.support
  /-- The map on the strict boundary, identified with the original toric boundary. -/
  boundaryMap : Dtor[Φ,h₀] ⟶ P.boundary
  /-- The boundary map is the restriction of the projection. -/
  boundary_comp : boundaryMap ≫ P.pair.hom.left = (Model[b,s,c]).2.boundaryι ≫ projection
  /-- The boundary map is over the common field. -/
  [boundary_over : boundaryMap.IsOver S]
  /-- The restriction is a subdivision with respect to the two oriented numberings. -/
  orientedSubdivision :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    boundaryMap.IsOrientedCycleSubdivision T P.cycle
  /-- The fixed toric component gives the initial component of the contracted cycle. -/
  component_zero :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    boundaryMap (T.componentGenericPoint origin) = P.cycle.componentGenericPoint 0
  /-- The contracted marking pulls back to the fixed inclusion in the auxiliary lattice. -/
  marked_pullback (a : L₁) :
    (Fan.internalBlowupPicardMarking b s (center c) hΦ).symm
      (Additive.ofMul (LineBundleClass.pullback projection (P.picardMarking a).toMul)) = ι a
  /-- The surface evaluation is the fixed-center evaluation descended along the projection. -/
  evaluation_eq : P.evaluation = Fan.contractedXEvaluation b s c hΦ projection

attribute [instance] ContractedToricFiber.modification ContractedToricFiber.boundary_over

variable {b s hΦ T origin ι}
  {c d : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {P Q : MarkedSurface ℂ n B₁ Xtor[r]}
  (p : ContractedToricFiber b s hΦ T origin ι c P)
  (q : ContractedToricFiber b s hΦ T origin ι d Q)

include p q in
private theorem boundaryCycleAction_eq_one_of_translation
    (e : P.pair ≅ Q.pair) (hc : Φ.IsComplete)
    {χ : Multiplicative (N →+ ℤ) →* ℂˣ} {t : (Model[b,s,c]).1 ≅ (Model[b,s,d]).1}
    (ht : IsLift (Φ.torusTranslation χ) (Model[b,s,c]).2.toTower (Model[b,s,d]).2.toTower t)
    (he : p.projection ≫ (surfaceIso e).hom = t.hom ≫ q.projection) :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
    (boundaryIso e).boundaryCycleAction P.cycle Q.cycle = 1 := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
  let τ := Fan.boundaryTranslation (Φ := Φ) χ
  have : IsClosedImmersion Q.pair.hom.left := Q.closedImmersion
  have hτ := Fan.commSq_boundaryTranslation_of_isLift b s c d p.boundary_comp q.boundary_comp
    (MarkedSurface.boundaryIso_hom_comp e) ht he
  have hτaction : τ.boundaryCycleAction T T = 1 :=
    Fan.boundaryCycleAction_boundaryTranslation hΦ hc
      ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) T χ
  have hsign := (boundaryIso e).cycleOrientationSign_eq_of_orientedCycleSubdivisions
    P.cycle Q.cycle T T τ p.orientedSubdivision q.orientedSubdivision hτ
  rw [hτaction, map_one] at hsign
  have hfixed := τ.apply_componentGenericPoint T T origin
  rw [hτaction, map_one, Equiv.Perm.one_apply] at hfixed
  dsimp only [τ] at hfixed
  have hzero := congrFun (congrArg (fun f : Dtor[Φ,h₀] ⟶ Q.boundary ↦ (f : Dtor[Φ,h₀] → Q.boundary))
    hτ.w) (T.componentGenericPoint origin)
  simp only [Scheme.Hom.comp_apply, hfixed, p.component_zero, q.component_zero] at hzero
  have hvertex := (boundaryIso e).apply_componentGenericPoint P.cycle Q.cycle 0
  rw [← hzero] at hvertex
  simpa using (eq_r_iff_cycleVertexPerm_zero_eq hsign).mpr
    (Q.cycle.componentGenericPoint_injective hvertex.symm)

include p q in
/-- For fixed targets from one ordered toric presentation, equality of X evaluations
along an isomorphism preserves the entire Picard marking and the ordered boundary action.
Finite index of the charges is used to identify the residual isomorphism as a translation. -/
theorem ContractedToricFiber.marked_actions_of_comp_evaluation_eq
    (e : P.pair ≅ Q.pair) (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (heval : (surfaceIso e).hom.toRationalMap.comp Q.evaluation = P.evaluation) :
    (∀ a, LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul =
      (P.picardMarking a).toMul) ∧
    (let : PrestableFamily (P.boundary ↘ S) := P.prestable
     letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
     (boundaryIso e).boundaryCycleAction P.cycle Q.cycle = 1) := by
  have : IsClosedImmersion P.pair.hom.left := P.closedImmersion
  have : IsClosedImmersion Q.pair.hom.left := Q.closedImmersion
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
  have : IsReduced P.boundary :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.boundary ↘ S)).isReduced
  have : IsReduced Q.boundary :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := Q.boundary ↘ S)).isReduced
  have : IsReduced P.pair.hom.left.ker.subscheme :=
    isReduced_of_isOpenImmersion (asIso P.pair.hom.left.toImage).inv
  have : IsReduced Q.pair.hom.left.ker.subscheme :=
    isReduced_of_isOpenImmersion (asIso Q.pair.hom.left.toImage).inv
  have : Q.surface.IsProjectiveOver ℂ := Q.projective
  rw [p.evaluation_eq, q.evaluation_eq] at heval
  obtain ⟨χ, ⟨t, ht, hcomp, -, hpic⟩, -⟩ :=
    Fan.existsUnique_translation_of_comp_contractedXEvaluation_eq b s c d hΦ
      p.projection q.projection (surfaceIso e) hindex p.projection_over q.projection_over
      p.support_comap q.support_comap heval
  refine ⟨fun a ↦ ?_, boundaryCycleAction_eq_one_of_translation p q e hc ht hcomp⟩
  have h := (hpic (Q.picardMarking a).toMul).trans (q.marked_pullback a)
  obtain ⟨a', ha'⟩ := P.picardMarking.surjective
    (Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul))
  have hcoord := p.marked_pullback a'
  rw [ha'] at hcoord
  have ha : a' = a := hι (hcoord.symm.trans h)
  rw [ha] at ha'
  exact congrArg Additive.toMul ha'.symm

/-- A pair isomorphism satisfying the same fixed-center X-evaluation square as a
realization has the same marked Picard pullback and ordered boundary action when both
targets belong to one ordered toric presentation with finite-index charges. -/
theorem FiberRealization.marked_actions_eq_of_compOfDefined
    {X₀ : Scheme} [IsIntegral X₀] [X₀.IsSeparated]
    {M : MarkedSurface ℂ n B₀ X₀} {F : X₀ ⤏ Xtor[r]}
    {I : B₁.IsometryEquiv B₀} {g : DihedralGroup n}
    (R : FiberRealization M P F I g)
    (p : ContractedToricFiber b s hΦ T origin ι c P)
    (q : ContractedToricFiber b s hΦ T origin ι d Q)
    (e : M.pair ≅ Q.pair) (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (he : ∃ h, M.evaluation.compOfDefined F h =
      (surfaceIso e).hom.toRationalMap.comp Q.evaluation) :
    (∀ a, M.picardMarking (I a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul)) ∧
    (letI : PrestableFamily (M.boundary ↘ S) := M.prestable
     letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
     (boundaryIso e).boundaryCycleAction M.cycle Q.cycle = g) := by
  obtain ⟨hpic, hbranch⟩ := p.marked_actions_of_comp_evaluation_eq q (R.targetIso e) hc hι hindex
    (R.comp_targetEvaluation_of_evaluation_eq e he)
  exact ⟨fun a ↦ (R.pullback_picardMarking_targetIso_eq_iff e a).mp (hpic a),
    (R.boundaryCycleAction_targetIso_eq_one_iff e).mp hbranch⟩

/-- At a common source center, the marked actions of two realizations of the same X map
coincide if their targets come from the same ordered toric presentation. -/
theorem FiberRealization.marked_actions_eq_of_contractedToricFiber
    {X₀ : Scheme} [IsIntegral X₀] [X₀.IsSeparated]
    {M : MarkedSurface ℂ n B₀ X₀} {F : X₀ ⤏ Xtor[r]}
    {I J : B₁.IsometryEquiv B₀} {g h : DihedralGroup n}
    (R : FiberRealization M P F I g) (R' : FiberRealization M Q F J h)
    (p : ContractedToricFiber b s hΦ T origin ι c P)
    (q : ContractedToricFiber b s hΦ T origin ι d Q)
    (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0) :
    I = J ∧ g = h := by
  obtain ⟨hp, hb⟩ :=
    R.marked_actions_eq_of_compOfDefined p q R'.iso hc hι hindex R'.evaluation_eq
  exact ⟨DFunLike.ext _ _ fun a ↦ M.picardMarking.injective ((hp a).trans (R'.picard_eq a).symm),
    hb.symm.trans R'.boundaryAction_eq⟩


open GeometricRealization (CenterPoint Point)

/-- Every center reached by a partial center map admits a contracted fiber
in the given ordered toric presentation of the target family. -/
abbrev GeometricRealization.HasToricTargetModels
    {T₀ T₁ : Over S} {P₁ : Point T₁ → MarkedSurface ℂ n B₁ Xtor[r]}
    (centers : Point T₁ → Multiplicative (Fin r → ℤ) →* ℂˣ)
    (C : T₀.left.PartialMap T₁.left) [C.IsOver T₀.hom T₁.hom] : Prop :=
  ∀ c : CenterPoint C, Nonempty
    (ContractedToricFiber b s hΦ T origin ι (centers (c ≫ C.domainTarget))
      (P₁ (c ≫ C.domainTarget)))

namespace GeometricRealization.HasToricTargetModels

variable {T₀ T₁ T₂ : Over S}
  {P₂ : Point T₂ → MarkedSurface ℂ n B₁ Xtor[r]}
  {centers : Point T₂ → Multiplicative (Fin r → ℤ) →* ℂˣ}
  {D : T₁.left.PartialMap T₂.left} [D.IsOver T₁.hom T₂.hom]

/-- A toric model at every target center supplies models for any partial center map. -/
theorem of_forall
    (h : ∀ c, Nonempty (ContractedToricFiber b s hΦ T origin ι (centers c) (P₂ c))) :
    HasToricTargetModels (T₀ := T₁) (T₁ := T₂) (b := b) (s := s) (hΦ := hΦ) (T := T)
      (origin := origin) (ι := ι) (P₁ := P₂) centers D :=
  fun c ↦ h (c ≫ D.domainTarget (X := T₁) (Y := T₂))

/-- Precomposing a partial center map preserves the target model condition. -/
theorem comp [PreirreducibleSpace T₀.left] [Nonempty T₁.left]
    (hD : HasToricTargetModels (T₀ := T₁) (T₁ := T₂) (b := b) (s := s) (hΦ := hΦ) (T := T)
      (origin := origin) (ι := ι) (P₁ := P₂) centers D)
    (C : T₀.left.PartialMap T₁.left) [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom] :
    HasToricTargetModels (T₀ := T₀) (T₁ := T₂) (b := b) (s := s) (hΦ := hΦ) (T := T)
      (origin := origin) (ι := ι) (P₁ := P₂) centers (C.comp D) :=
  C.forall_comp_domainTarget (X := T₀) (Y := T₁) (Z := T₂) D
    (fun c ↦ Nonempty (ContractedToricFiber b s hΦ T origin ι (centers c) (P₂ c))) hD

end GeometricRealization.HasToricTargetModels

variable
  {T₀ T₁ : Over S} [Nonempty T₀.left] [Smooth T₀.hom]
  {X₀ : Scheme} [IsIntegral X₀] [X₀.IsSeparated]
  {P₀ : Point T₀ → MarkedSurface ℂ n B₀ X₀} {P₁ : Point T₁ → MarkedSurface ℂ n B₁ Xtor[r]}
  {C D : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [IsDominant D.hom]
  [C.IsOver T₀.hom T₁.hom] [D.IsOver T₀.hom T₁.hom]
  {F G : X₀ ⤏ Xtor[r]} [F.IsDominant] [G.IsDominant]

/-- Two geometric realizations of the same X map have the same marked Picard pullback and
ordered boundary action when their target fibers are contracted models of a fixed ordered
toric presentation with finite-index charges. The center maps may have different domains
and may take different values at the common source center. -/
theorem GeometricRealization.marked_actions_eq_of_xMap_eq
    (R : GeometricRealization P₀ P₁ C F) (R' : GeometricRealization P₀ P₁ D G)
    (hFG : F = G) (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0)
    (centers : Point T₁ → (Multiplicative (Fin r → ℤ) →* ℂˣ))
    (hC : HasToricTargetModels (b := b) (s := s) (hΦ := hΦ) (T := T)
      (origin := origin) (ι := ι) (P₁ := P₁) centers C)
    (hD : HasToricTargetModels (b := b) (s := s) (hΦ := hΦ) (T := T)
      (origin := origin) (ι := ι) (P₁ := P₁) centers D) :
    R.picard = R'.picard ∧ R.boundaryAction = R'.boundaryAction := by
  subst G
  let W := C.domain ⊓ D.domain
  have hW : Dense (W : Set T₀.left) :=
    C.dense_domain.inter_of_isOpen_left D.dense_domain C.domain.is_open'
  have : Nonempty W.toScheme := hW.nonempty.to_subtype
  have : Smooth (W.ι ≫ T₀.hom) := inferInstance
  obtain ⟨⟨x, hx⟩⟩ := (W.ι ≫ T₀.hom).denseRange_rationalSections.nonempty
  have hWC : W ≤ C.domain := inf_le_left
  have hWD : W ≤ D.domain := inf_le_right
  let x₀ : CenterPoint C := Over.homMk (x ≫ T₀.left.homOfLE hWC) (by simp [hx])
  let x₁ : CenterPoint D := Over.homMk (x ≫ T₀.left.homOfLE hWD) (by simp [hx])
  have hsource : x₀ ≫ C.domainSource = x₁ ≫ D.domainSource := by
    ext : 1
    simp [x₀, x₁]
  obtain ⟨p⟩ := hC x₀
  obtain ⟨q⟩ := hD x₁
  have R₁ : FiberRealization (P₀ (x₀ ≫ C.domainSource)) (P₁ (x₁ ≫ D.domainTarget))
      F R'.picard R'.boundaryAction := hsource ▸ R'.fiber x₁
  exact (R.fiber x₀).marked_actions_eq_of_contractedToricFiber R₁ p q hc hι hindex

end ContractedToric

end QPainleve.SignedClusterModularGroup
