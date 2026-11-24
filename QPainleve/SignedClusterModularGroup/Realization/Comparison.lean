/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Comparing geometric realizations

The fixed-center evaluation squares of two realizations turn agreement of their
target evaluations into agreement of the two X maps on a dominant source chart.
This computes the rational compositions on their defined domains.

Conversely, agreement of the X maps gives a comparison of target evaluations.
The residual target isomorphism compares the marked Picard and boundary actions.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.SignedClusterModularGroup.FiberRealization

open MarkedSurface (surfaceIso boundaryIso)

section SourceChart

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L L' : Type u} [AddCommGroup L] [AddCommGroup L']
  {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
  {X X' W : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [X'.IsSeparated] [IsIntegral W]
  {M : MarkedSurface k n B X} {N N' : MarkedSurface k n B' X'}
  {F G : X ⤏ X'} {I J : B'.IsometryEquiv B} {g h : DihedralGroup n}

/-- If two fixed-center realizations yield the same target evaluation on their
common source surface, the induced rational compositions agree on every
dominant chart of that source. -/
theorem exists_compOfDefined_eq_of_target_evaluation_eq
    (R : FiberRealization M N F I g) (R' : FiberRealization M N' G J h)
    (i : W ⤏ M.surface) [i.IsDominant]
    (heq : (surfaceIso R.iso).hom.toRationalMap.comp N.evaluation =
      (surfaceIso R'.iso).hom.toRationalMap.comp N'.evaluation) :
    let e := i.comp M.evaluation
    let x := e.fromFunctionField (IsLocalRing.closedPoint W.functionField)
    ∃ (hf : x ∈ F.domain) (hg : x ∈ G.domain),
      e.compOfDefined F hf = e.compOfDefined G hg := by
  obtain ⟨hf, hF⟩ := R.evaluation_eq
  obtain ⟨hg, hG⟩ := R'.evaluation_eq
  obtain ⟨hf', heF⟩ := i.comp_compOfDefined M.evaluation F hf
  obtain ⟨hg', heG⟩ := i.comp_compOfDefined M.evaluation G hg
  have h := congrArg (i.comp ·) (hF.trans (heq.trans hG.symm))
  exact ⟨hf', hg', heF.trans (h.trans heG.symm)⟩

end SourceChart

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L L' : Type u} [AddCommGroup L] [AddCommGroup L']
  {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
  {X X' : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [X'.IsSeparated]
  {M : MarkedSurface k n B X} {P Q : MarkedSurface k n B' X'}
  {F : X ⤏ X'} {I J : B'.IsometryEquiv B} {g h : DihedralGroup n}
  (R : FiberRealization M P F I g)

/-- A specified isomorphism satisfying the evaluation square of a realized X map
induces a residual isomorphism intertwining the two target evaluations. -/
theorem comp_targetEvaluation_of_evaluation_eq (e : M.pair ≅ Q.pair)
    (he : ∃ h, M.evaluation.compOfDefined F h =
      (surfaceIso e).hom.toRationalMap.comp Q.evaluation) :
    (surfaceIso (R.iso.symm ≪≫ e)).hom.toRationalMap.comp Q.evaluation = P.evaluation := by
  obtain ⟨_, hR⟩ := R.evaluation_eq
  obtain ⟨_, hR'⟩ := he
  apply Scheme.RationalMap.comp_left_injective (surfaceIso R.iso).hom.toRationalMap
  simpa only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
    Scheme.Hom.toRationalMap_compHom, MarkedSurface.surfaceIso_trans,
    MarkedSurface.surfaceIso_symm, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    using hR'.symm.trans hR

/-- The residual isomorphism of the target pairs intertwines their X evaluations when the
source realization uses the same rational map. -/
theorem comp_targetEvaluation (R' : FiberRealization M Q F J h) :
    (surfaceIso (R.iso.symm ≪≫ R'.iso)).hom.toRationalMap.comp Q.evaluation = P.evaluation :=
  R.comp_targetEvaluation_of_evaluation_eq R'.iso R'.evaluation_eq

variable {G : X ⤏ X'} (R' : FiberRealization M Q G J h)

/-- Equality of the Picard actions makes the residual isomorphism identify the two
target markings. -/
theorem pullback_picardMarking_targetIso (hI : I = J) (a : L') :
    LineBundleClass.pullback (surfaceIso (R.iso.symm ≪≫ R'.iso)).hom
      (Q.picardMarking a).toMul = (P.picardMarking a).toMul := by
  apply (LineBundleClass.pullbackEquiv (surfaceIso R.iso)).injective
  have ha := congrArg Additive.toMul ((R'.picard_eq a).symm.trans
    ((congrArg (fun f : B'.IsometryEquiv B ↦ M.picardMarking (f a)) hI).symm.trans
      (R.picard_eq a)))
  simpa only [LineBundleClass.pullbackEquiv_apply, LineBundleClass.pullback_comp,
    MarkedSurface.surfaceIso_trans, MarkedSurface.surfaceIso_symm, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, toMul_ofMul] using ha

/-- If the residual target isomorphism preserves each marked Picard class, the two Picard
pullbacks agree. -/
theorem picard_eq_of_pullback_targetIso
    (hp : ∀ a, LineBundleClass.pullback (surfaceIso (R.iso.symm ≪≫ R'.iso)).hom
      (Q.picardMarking a).toMul =
      (P.picardMarking a).toMul) :
    I = J := by
  apply DFunLike.ext
  intro a
  apply M.picardMarking.injective
  rw [R.picard_eq, R'.picard_eq, ← hp a, LineBundleClass.pullback_comp]
  simp only [MarkedSurface.surfaceIso_trans, MarkedSurface.surfaceIso_symm, Iso.trans_hom,
    Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- Equality of the boundary actions makes the residual isomorphism preserve every
numbered branch. -/
theorem boundaryCycleAction_targetIso (hg : g = h) :
    letI : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
    letI : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
    (boundaryIso (R.iso.symm ≪≫ R'.iso)).boundaryCycleAction P.cycle Q.cycle = 1 := by
  let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  let : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
  let : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
  have hpair : R.iso ≪≫ (R.iso.symm ≪≫ R'.iso) = R'.iso := by simp
  have hcomp := (boundaryIso R.iso).boundaryCycleAction_trans M.cycle P.cycle
    (boundaryIso (R.iso.symm ≪≫ R'.iso)) Q.cycle
  have hmul : h = (boundaryIso (R.iso.symm ≪≫ R'.iso)).boundaryCycleAction P.cycle Q.cycle * h := by
    simpa only [← MarkedSurface.boundaryIso_trans, hpair, R'.boundaryAction_eq,
      R.boundaryAction_eq, hg] using hcomp
  exact mul_right_cancel ((one_mul h).trans hmul).symm

/-- If the residual target isomorphism preserves the numbered branches, the two actions
agree on the entire boundary. -/
theorem boundaryAction_eq_of_targetIso
    (hb : letI : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
          letI : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
          (boundaryIso (R.iso.symm ≪≫ R'.iso)).boundaryCycleAction P.cycle Q.cycle = 1) :
    g = h := by
  let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  let : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
  let : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
  have hpair : R.iso ≪≫ (R.iso.symm ≪≫ R'.iso) = R'.iso := by simp
  have hcomp := (boundaryIso R.iso).boundaryCycleAction_trans M.cycle P.cycle
    (boundaryIso (R.iso.symm ≪≫ R'.iso)) Q.cycle
  simpa only [← MarkedSurface.boundaryIso_trans, hpair, R'.boundaryAction_eq,
    hb, R.boundaryAction_eq, one_mul] using hcomp.symm

end QPainleve.SignedClusterModularGroup.FiberRealization
