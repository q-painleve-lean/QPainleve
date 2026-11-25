/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Word.Endpoint
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.PicardAction

import QPainleve.SignedClusterModularGroup.Realization.Specialization

/-!
# Prescribed Picard actions from resolved changes of presentation

A resolved presentation change gives a word by comparing the fixed-center evaluations
on the resolving surface. At a center where the word has a geometric realization,
the evaluation square identifies its Picard pullback and ordered branch action with
those of the prescribed pair isomorphism. This comparison allows the word's center
map to reach a different point of the target presentation.

The word is supplied by
`Fan.LogarithmicProjection.exists_word_of_resolved_sarkisov_path_to_model`; the marked
comparison uses `FiberRealization.marked_actions_eq_of_compOfDefined_on_resolution`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "src[" C "," x "]" =>
  x ≫ PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst[" C "," x "]" =>
  x ≫ PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P

open MarkedSurface (surfaceIso boundaryIso)
open SignedBoundaryIsometryGroup (sign toIsometry)

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
    (e : (M (src[C,x])).pair ≅ (M c₁).pair) (π : Z ⤏ (M (src[C,x])).surface) [π.IsDominant]
    (he : ∃ h, (π.comp (M (src[C,x])).evaluation).compOfDefined (w.xRationalMap ℂ) h =
      π.comp ((surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation))
    (hpic : ∀ a, (M (src[C,x])).picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking a).toMul))
    (hsgn : letI : PrestableFamily ((M (src[C,x])).boundary ↘ S) := (M (src[C,x])).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M (src[C,x])).cycle (M c₁).cycle) = sign B d g) :
    ρ eval[E,w] = g := by
  let : IsIntegral (M (src[C,x])).surface := (M (src[C,x])).integral
  let : (M (src[C,x])).surface.IsProjectiveOver ℂ := (M (src[C,x])).projective
  obtain ⟨hI, hbranch⟩ := (R.fiber x).marked_actions_eq_of_compOfDefined_on_resolution
    p q e π Q.complete hι hindex he
  rw [hρ]
  apply Subtype.ext
  rw [coe_toSignedBoundaryIsometry]
  rw [SignedBoundaryIsometryGroup.sign_apply] at hsgn
  refine Prod.ext ?_ (R.orientation_def.trans ((congrArg DihedralGroup.cycleOrientationSign
    hbranch).symm.trans hsgn))
  apply Subtype.ext
  apply LinearEquiv.ext
  intro a
  rw [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  rw [SignedBoundaryIsometryGroup.toIsometry_apply] at hpic
  exact (M (src[C,x])).picardMarking.injective ((hI a).trans (hpic a).symm)

/-- A loop whose evaluation realizes the specified pair isomorphism on a resolution
represents the isomorphism's signed Picard action. When that action has positive sign,
there is an inversion-free representative with the same X pullback. -/
theorem exists_word_signedPicardHom_eq_of_pair_iso_on_resolution
    (P : ChargeSeed E N) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ))
    (hρ : ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (hparity : sign B d (ρ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount)
    {c₀ c₁ : Point Centers[r]} (hc₀ : c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (hp : Models[Cw[w,P]])
    (q : Model[c₁]) (hι : Function.Injective Q.inclusion)
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0)
    (e : (M c₀).pair ≅ (M c₁).pair) (π : Z ⤏ (M c₀).surface) [π.IsDominant]
    (he : ∃ h, (π.comp (M c₀).evaluation).compOfDefined (w.xRationalMap ℂ) h =
      π.comp ((surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation))
    (hpic : ∀ a, (M c₀).picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking a).toMul))
    (hsgn : letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M c₀).cycle (M c₁).cycle) = sign B d g) :
    ∃ v : Word E E, v.xPullback ℂ = w.xPullback ℂ ∧ ρ eval[E,v] = g ∧
      (sign B d g = 1 → v.inversionCount = 0) := by
  have hc : c₀.left (default : S) ∈ Cw[w,P].domain := by
    rwa [Quiver.Path.centerPartialMap_domain]
  obtain ⟨x, hx⟩ := (Cw[w,P].exists_section_comp_domainSource_eq_iff
    (Y := Centers[r]) c₀ (default : S)).mpr hc
  obtain ⟨p⟩ := hp x
  subst c₀
  have hvalue := signedPicardHom_apply_of_pair_iso_on_resolution R hρ x p q hι hindex
    e π he hpic hsgn
  by_cases hpos : sign B d g = 1
  · have heven := (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp
      (hparity.symm.trans ((congrArg (sign B d) hvalue).trans hpos))
    obtain ⟨v, hv, hxv⟩ := w.exists_xPullback_eq_of_even_inversionCount ℂ heven
    have hvw := (signedClusterModularGroupMap_eq_iff ℂ E (End.of v) (End.of w)).mpr hxv.symm
    exact ⟨v, hxv.symm, (congrArg (fun z ↦ ρ (op z)) hvw).trans hvalue, fun _ ↦ hv⟩
  · exact ⟨w, rfl, hvalue, fun hs ↦ (hpos hs).elim⟩

open Fan Fan.LogarithmicProjection
open scoped Sarkisov

variable [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)] [Z.IsProjectiveOver ℂ]
  {D : Z.IdealSheafData} {A A' : LogarithmicProjection i D}

/-- A resolved Sarkisov path between the two marked fibers of a specified pair isomorphism
gives a loop with the isomorphism's signed Picard action. The source center is chosen in
all loop noncollision opens before reading the path. The ordered endpoint evaluations
are compared on the given resolving surface. For a positive action the loop is
inversion-free. -/
theorem exists_word_signedPicardHom_eq_of_resolved_sarkisov_path
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
    (e : (M c₀).pair ≅ (M c₁).pair) (π : Z ⤏ (M c₀).surface) [π.IsDominant]
    (hev₀ : U.xEvaluation = π.comp (M c₀).evaluation)
    (hev₁ : U'.xEvaluation = π.comp ((surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation))
    (hpic : ∀ a, (M c₀).picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking a).toMul))
    (hsgn : letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M c₀).cycle (M c₁).cycle) = sign B d g) :
    ∃ v : Word E E, ρ eval[E,v] = g ∧ (sign B d g = 1 → v.inversionCount = 0) ∧
      ∃ h, U.xEvaluation.compOfDefined (v.xRationalMap ℂ) h = U'.xEvaluation := by
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
      π.comp ((surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation) := by
    rw [hF, ← hev₀, ← hev₁]
    exact hu
  obtain ⟨⟨R⟩, hm⟩ := hreal v
  obtain ⟨v', hv', hvalue, hfree⟩ := exists_word_signedPicardHom_eq_of_pair_iso_on_resolution
    P R (hρ v R hm) (hparity v) (hgeneric v) hm q hι hindex e π he hpic hsgn
  refine ⟨v', hvalue, hfree, ?_⟩
  rw [(Quiver.Path.xRationalMap_eq_iff ℂ v' v).mpr hv', hF]
  exact hu

end QPainleve.SignedClusterModularGroup.GeometricRealization
