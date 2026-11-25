/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Surjectivity

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.PairIso
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.MarkedFactorization

/-!
# Cluster loops realizing specified isomorphisms of marked fibers

The common ordered models of a pair isomorphism are the endpoints of the resolved
factorization. Reading the factorization in the original seed produces a loop with the
specified Picard pullback and branch sign, and the evaluation square descends to the
source fiber.

The geometric inputs are `CompleteToricPresentation.exists_common_ordered_models_of_pair_iso`
and the resolved factorization in [Lutz, Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=68).
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Scheme
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Fan Fan.LogarithmicProjection

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open MarkedSurface (surfaceIso boundaryIso)
open SignedBoundaryIsometryGroup (sign toIsometry)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" =>
  (LineBundleClass.mk (Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} {Q : CompleteToricPresentation i b r L γ}
  {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]}
  {d : ZMod n → L} {hD : ∀ c, D[M c].IsEffectiveCartier}
  {hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j}

local instance instNonemptyCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instPrestableBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable
local instance instNeZeroBoundaryLength : NeZero Q.length := Q.neZero

local notation "Models[" C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
    (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
    (fun c ↦ χ[c]) C

/-- A specified isomorphism of two fibers of a marked toric presentation gives a
loop with the same Picard pullback, branch sign, and fixed-center X evaluation.
If the specified action preserves orientation, the loop uses no inversions. -/
theorem exists_word_signedPicardHom_eq_of_pair_iso
    (P : ChargeSeed E N) (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (models : ∀ c : Point Centers[r], c.left (default : S) ∈ Quiver.Path.nil.centerOpen ℂ P →
      Q.HasNodalModel c (M c))
    {c₀ c₁ : Point Centers[r]} (hP : Q.HasNodalModel c₁ (M c₁))
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (hgeneric : ∀ w : Word E E, c₀.left (default : S) ∈ w.centerOpen ℂ P)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (hρ : ∀ (w : Word E E) (R : GeometricRealization M M Cw[w,P] (w.xRationalMap ℂ)),
      Models[Cw[w,P]] → ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark)
    (e : (M c₀).pair ≅ (M c₁).pair) {g : signedBoundaryIsometryGroup B d}
    (hpic : ∀ a, (M c₀).picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom ((M c₁).picardMarking a).toMul))
    (hsgn : letI : PrestableFamily ((M c₀).boundary ↘ S) := (M c₀).prestable
      letI : PrestableFamily ((M c₁).boundary ↘ S) := (M c₁).prestable
      DihedralGroup.cycleOrientationSign ((boundaryIso e).boundaryCycleAction
        (M c₀).cycle (M c₁).cycle) = sign B d g) :
    letI : IsIntegral (M c₀).surface := (M c₀).integral
    ∃ w : Word E E, ρ eval[E,w] = g ∧ (sign B d g = 1 → w.inversionCount = 0) ∧
      ∃ h, (M c₀).evaluation.compOfDefined (w.xRationalMap ℂ) h =
        (surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation := by
  let : IsIntegral (M c₀).surface := (M c₀).integral
  let : IsIntegral (M c₁).surface := (M c₁).integral
  let : (M c₀).surface.IsProjectiveOver ℂ := (M c₀).projective
  let : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
  let : Smooth ((M c₀).surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian (M c₀).surface := isNoetherian_of_finiteType ((M c₀).surface ↘ S)
  have hM := models c₀ (hgeneric Quiver.Path.nil)
  let := hM.isRationalOver
  obtain ⟨_, W, T, hT, π, s, hSm, hmod, hπ, hs, A, A', U, U', hCartier, -, -, hA, hA', hU, hU',
    hev₀, hev₁⟩ := Q.exists_common_ordered_models_of_pair_iso hM hP e (hD c₀) (hD c₁)
  subst s π
  let : W.Over S := ⟨T.toBase ≫ (M c₀).surface ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) := hSm
  let : IsIntegral W := hT.isClosedPointTower.isIntegral ((M c₀).surface ↘ S)
  let : W.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : IsNoetherian W := isNoetherian_of_finiteType (W ↘ S)
  let : IsModification A.hom := hA
  let : IsModification A'.hom := hA'
  let : IsModification T.toBase := hmod
  have hNode := (hT.radical_comap_toBase (hD c₀) (M c₀).boundaryIdeal_nodal).2
  have hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) :=
    P.matrix_eq.symm.trans (congrArg₂ chargeExchangeMatrix hform hcharge)
  have hm : U.exchangeMatrix = E := SkewExchangeMatrix.ext (hU.trans hE.symm)
  have hm' : U'.exchangeMatrix = E := SkewExchangeMatrix.ext (hU'.trans hE.symm)
  have hev : U'.xEvaluation = T.toBase.toRationalMap.comp
      ((surfaceIso e).hom.toRationalMap.comp (M c₁).evaluation) := by
    simpa only [← RationalMap.comp_assoc, RationalMap.comp_toRationalMap,
      Hom.toRationalMap_compHom] using hev₁
  have hfactor := exists_resolved_sarkisov_factorization b Q.fan.lattice A A' hCartier hNode
  have hcan := congrArg Inv.inv (hM.canonicalClass (hD c₀))
  exact exists_word_signedPicardHom_eq_of_resolved_sarkisov_factorization
    hfactor U U' hCartier hm hm' P hform hcharge models hP hnef hsq hcan hprim hgeneric ρ hρ
    e T.toBase.toRationalMap hev₀ hev hpic hsgn

end QPainleve.SignedClusterModularGroup.GeometricRealization
