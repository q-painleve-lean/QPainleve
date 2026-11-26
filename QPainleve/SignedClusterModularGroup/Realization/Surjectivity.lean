/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Endpoint
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction
public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.LoopRealization

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Prescribed Picard actions from resolved changes of presentation

A resolved presentation change gives a word by comparing the fixed-center evaluations
on the resolving surface. At a center where the word has a geometric realization,
the evaluation square identifies its Picard pullback and ordered branch action with
those of the prescribed pair isomorphism. This comparison allows the word's center
map to reach a different point of the target presentation.

The word is supplied by
`Fan.LogarithmicProjection.exists_word_of_resolved_sarkisov_path_to_model`; the marked
comparison uses `FiberRealization.marked_actions_eq_of_compOfDefined` after descending
the evaluation square to the source surface.
For a factorization on a nodal refinement, the fixed-center evaluation also
descends to the original marked surface.

A `PicardLoopRealization` records the chosen loop, its signed Picard action,
and its evaluation equation.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "src[" C "," x "]" =>
  x ≫ PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P

open MarkedSurface (surfaceIso)
open SignedBoundaryIsometryGroup (sign)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L} {hD : ∀ c, D[M c].IsEffectiveCartier}
  {hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j}
  {Q : CompleteToricPresentation i b r L γ}

local instance instNonemptySurjectivityCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instPrestableSurjectivityBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable
local instance instNeZeroSurjectivityBoundaryLength : NeZero Q.length := Q.neZero

local notation "Model[" c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] (M c)
local notation "Models[" C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun c ↦ χ[c]) C

variable {Z : Scheme} [IsIntegral Z] {w : Word E E}
  {ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d}
  {g : signedBoundaryIsometryGroup B d}

/-- The signed Picard action of a loop equals the prescribed action of a pair isomorphism
if the loop and the isomorphism give the same fixed-center evaluation on a dominating
surface. The reached center and the prescribed target center can differ. The comparison
uses the full marked pullback and the sign on the ordered branches. -/
theorem signedPicardHom_apply_of_pair_iso_on_resolution
    {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
    [C.IsOver Centers[r].hom Centers[r].hom]
    (R : GeometricRealization M M C (w.xRationalMap ℂ))
    (hρ : ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C)
    {c₁ : Point Centers[r]} (p : Model[dst[C,x]]) (q : Model[c₁])
    (hι : Function.Injective Q.inclusion)
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0)
    (e : SignedPicardPairIso (M (src[C,x])) (M c₁) g)
    (π : Z ⤏ (M (src[C,x])).surface) [π.IsDominant]
    (he : ∃ h, (π.comp (M (src[C,x])).evaluation).compOfDefined (w.xRationalMap ℂ) h =
      π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation)) :
    ρ eval[E,w] = g := by
  let : IsIntegral (M (src[C,x])).surface := (M (src[C,x])).integral
  let : (M (src[C,x])).surface.IsProjectiveOver ℂ := (M (src[C,x])).projective
  obtain ⟨hI, hbranch⟩ := (R.fiber x).marked_actions_eq_of_compOfDefined p q e.iso Q.complete hι
    hindex ((π.compOfDefined_eq_iff_of_dominant _ _ _).mp he)
  rw [hρ]
  apply Subtype.ext
  rw [coe_toSignedBoundaryIsometry]
  have hsgn := (SignedBoundaryIsometryGroup.sign_apply B d g) ▸ e.sign_eq
  refine Prod.ext ?_ (R.orientation_def.trans ((congrArg DihedralGroup.cycleOrientationSign
    hbranch).symm.trans hsgn))
  apply Subtype.ext
  apply LinearEquiv.ext
  intro a
  rw [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  have hpic := e.picard_eq a
  rw [SignedBoundaryIsometryGroup.toIsometry_apply] at hpic
  exact (M (src[C,x])).picardMarking.injective ((hI a).trans hpic.symm)

/-- A loop whose evaluation realizes the specified pair isomorphism on a resolution
represents the isomorphism's signed Picard action. When that action has positive sign,
there is an inversion-free representative with the same X pullback. -/
theorem exists_picardLoopRealization_of_pair_iso_on_resolution
    (P : ChargeSeed E N) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ))
    (hρ : ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (hparity : sign B d (ρ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount)
    {c₀ c₁ : Point Centers[r]} (hc₀ : c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (hp : Models[Cw[w,P]])
    (q : Model[c₁]) (hι : Function.Injective Q.inclusion)
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0)
    (e : SignedPicardPairIso (M c₀) (M c₁) g) (π : Z ⤏ (M c₀).surface) [π.IsDominant]
    (he : ∃ h, (π.comp (M c₀).evaluation).compOfDefined (w.xRationalMap ℂ) h =
      π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation)) :
    ∃ v : PicardLoopRealization ρ g (π.comp (M c₀).evaluation)
        (π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation)),
      v.word.xPullback ℂ = w.xPullback ℂ := by
  have hc : c₀.left (default : S) ∈ Cw[w,P].domain := by
    rwa [Quiver.Path.centerPartialMap_domain]
  obtain ⟨x, hx⟩ := (Cw[w,P].exists_section_comp_domainSource_eq_iff
    (Y := Centers[r]) c₀ (default : S)).mpr hc
  obtain ⟨p⟩ := hp x
  subst c₀
  have hvalue := signedPicardHom_apply_of_pair_iso_on_resolution R hρ x p q hι hindex
    e π he
  obtain ⟨v, hvw, hv⟩ : ∃ v : Word E E, v.xPullback ℂ = w.xPullback ℂ ∧
      (sign B d g = 1 → v.inversionCount = 0) := by
    by_cases hpos : sign B d g = 1
    · have heven := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp
        (hparity.symm.trans ((congrArg (sign B d) hvalue).trans hpos))
      obtain ⟨v, hv, hxv⟩ := w.exists_xPullback_eq_of_even_inversionCount ℂ heven
      exact ⟨v, hxv.symm, fun _ ↦ hv⟩
    · exact ⟨w, rfl, fun hs ↦ (hpos hs).elim⟩
  have hmap := (signedClusterModularGroupMap_eq_iff ℂ E (End.of v) (End.of w)).mpr hvw
  refine ⟨⟨v, (congrArg (fun z ↦ ρ (op z)) hmap).trans hvalue, hv, ?_⟩, hvw⟩
  rwa [(Quiver.Path.xRationalMap_eq_iff ℂ v w).mpr hvw]

open Fan Fan.LogarithmicProjection
open scoped Sarkisov

variable [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [Z.IsProjectiveOver ℂ]
  {D : Z.IdealSheafData} {A A' : LogarithmicProjection i D}

/-- A resolved Sarkisov path between the two marked fibers of a specified pair isomorphism
gives a loop with the isomorphism's signed Picard action. The source center is chosen in
all loop noncollision opens before reading the path. The ordered endpoint evaluations
are compared on the given resolving surface. For a positive action the loop is
inversion-free. -/
theorem nonempty_picardLoopRealization_of_resolved_sarkisov_path
    (P : ChargeSeed E N) (path : SarkisovPath A A')
    (U : OrderedToricModel A r) (U' : OrderedToricModel A' r)
    (hU : U.exchangeMatrix = E) (hU' : U'.exchangeMatrix = E)
    {c₀ c₁ : Point Centers[r]} (q : Model[c₁])
    (hι : Function.Injective Q.inclusion)
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0)
    (hgeneric : ∀ v : Word E E, c₀.left (default : S) ∈ v.centerOpen ℂ P)
    (hreal : ∀ v : Word E E, Nonempty (GeometricRealization M M Cw[v,P] (v.xRationalMap ℂ)) ∧
      Models[Cw[v,P]])
    (hρ : ∀ (v : Word E E) (R : GeometricRealization M M Cw[v,P] (v.xRationalMap ℂ)),
      Models[Cw[v,P]] → ρ eval[E,v] = R.toSignedBoundaryIsometry d hD hmark)
    (hparity : ∀ v : Word E E, sign B d (ρ eval[E,v]) = (-1 : ℤˣ) ^ v.inversionCount)
    (e : SignedPicardPairIso (M c₀) (M c₁) g) (π : Z ⤏ (M c₀).surface) [π.IsDominant]
    (hev₀ : U.xEvaluation = π.comp (M c₀).evaluation)
    (hev₁ : U'.xEvaluation = π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation)) :
    Nonempty (PicardLoopRealization ρ g U.xEvaluation U'.xEvaluation) := by
  obtain ⟨_, _, _, u, _, _, -, -, -, -, -, -, -, -, -, -, -, hu⟩ :=
    exists_word_of_resolved_sarkisov_path_to_model path U U'
  let v : Word E E := cast (congrArg₂ (fun a b ↦ Word a b) hU hU') u
  have hF : v.xRationalMap ℂ = u.xRationalMap ℂ := by
    dsimp only [v]
    generalize U.exchangeMatrix = E₀ at u hU ⊢
    generalize U'.exchangeMatrix = E₁ at u hU' ⊢
    subst E₀ E₁
    rfl
  have he : ∃ h, (π.comp (M c₀).evaluation).compOfDefined (v.xRationalMap ℂ) h =
      π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation) := by
    rw [hF, ← hev₀, ← hev₁]
    exact hu
  obtain ⟨⟨R⟩, hm⟩ := hreal v
  obtain ⟨v', -⟩ := exists_picardLoopRealization_of_pair_iso_on_resolution
    P R (hρ v R hm) (hparity v) (hgeneric v) hm q hι hindex e π he
  rw [hev₀, hev₁]
  exact ⟨v'⟩

/-- A loop intertwining the fixed-center evaluation of a specified pair isomorphism
gives the prescribed signed Picard action. For a positive action an inversion-free
loop has the same fixed-center evaluation. -/
theorem nonempty_picardLoopRealization_of_comp_evaluation_eq
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Quiver.Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c₀ c₁ : Point Centers[r]}
    (hP : Q.HasNodalModel c₁ (M c₁))
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (hρ : ∀ (w : Word E E) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ)),
      Models[Cw[w,P]] → ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (e : SignedPicardPairIso (M c₀) (M c₁) g) (w : Word E E)
    (hc₀ : c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (heval : letI : IsIntegral (M c₀).surface := (M c₀).integral
      ∃ h, (M c₀).evaluation.compOfDefined (w.xRationalMap ℂ) h =
        (surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation) :
    letI : IsIntegral (M c₀).surface := (M c₀).integral
    Nonempty (PicardLoopRealization ρ g (M c₀).evaluation
      ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation)) := by
  let : IsIntegral (M c₀).surface := (M c₀).integral
  let := Q.complete.nonempty_cones
  let := Q.neZero
  let := Q.prestable
  have hE := P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hM := models c₀ (w.centerOpen_le_centerOpen_nil ℂ P hc₀)
  have hindex := hM.chargeIndex_ne_zero (hD c₀) hnef hsq hprim
  have hker : E.matrix.mulVecLin.ker = P.charge.ker := by
    rw [hE, hcharge]
    exact Fan.ker_chargeExchangeMatrix_rayChargeMap b Q.rays hindex
  obtain ⟨R, hη, _, htarget⟩ := exists_realize_signed_loop w P Q hform hcharge M
    (fun x ↦ models _ (Quiver.Path.nil.centerPoint_endpoints_mem_noncollision P hker x).2)
    hM hD hnef hsq hprim d hmark
  have htargets : Models[Cw[w,P]] := fun x ↦ (htarget x).nonempty_contractedToricFiber
  obtain ⟨q, _⟩ := (Q.hasNodalModel_iff c₁ (M c₁)).mp hP
  have hvalue := hρ w R htargets
  have hparity : sign B d (ρ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount := by
    rw [hvalue, SignedBoundaryIsometryGroup.sign_apply, coe_toSignedBoundaryIsometry, hη]
  let π := RationalMap.id (M c₀).surface
  have hw : ∃ h, (π.comp (M c₀).evaluation).compOfDefined (w.xRationalMap ℂ) h =
      π.comp ((surfaceIso e.iso).hom.toRationalMap.comp (M c₁).evaluation) :=
    by simpa only [π, RationalMap.id_comp] using heval
  obtain ⟨v, -⟩ := exists_picardLoopRealization_of_pair_iso_on_resolution
    P R hvalue hparity hc₀ htargets q (Q.inclusion_injective hM)
    hindex e π hw
  exact ⟨by simpa only [π, RationalMap.id_comp] using v⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization
