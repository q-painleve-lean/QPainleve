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
  {F : X ⤏ X'} {I : B'.IsometryEquiv B} {g : DihedralGroup n}
  (R : FiberRealization M P F I g)

/-- The isomorphism from the realized target to the target of another isomorphism
out of the same source pair. -/
noncomputable def targetIso {T : Arrow (Over (Spec (.of k)))} (e : M.pair ≅ T) :
    P.pair ≅ T :=
  R.iso.symm ≪≫ e

/-- Comparing the realization with its own pair isomorphism gives the identity. -/
@[simp]
theorem targetIso_self : R.targetIso R.iso = Iso.refl P.pair := by
  simp [targetIso]

/-- Composing the realized isomorphism with the target isomorphism recovers the
other isomorphism from the source. -/
@[simp]
theorem iso_trans_targetIso {T : Arrow (Over (Spec (.of k)))} (e : M.pair ≅ T) :
    R.iso ≪≫ R.targetIso e = e := by
  simp [targetIso]

/-- The target isomorphism intertwines the evaluations exactly when their pullbacks
to the common source pair agree. -/
theorem comp_targetEvaluation_eq_iff (e : M.pair ≅ Q.pair) :
    (surfaceIso (R.targetIso e)).hom.toRationalMap.comp Q.evaluation = P.evaluation ↔
    (surfaceIso e).hom.toRationalMap.comp Q.evaluation =
      (surfaceIso R.iso).hom.toRationalMap.comp P.evaluation := by
  rw [← (Scheme.RationalMap.comp_left_injective
    (Z := X') (surfaceIso R.iso).hom.toRationalMap).eq_iff]
  simp only [← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
    Scheme.Hom.toRationalMap_compHom, ← Iso.trans_hom, ← MarkedSurface.surfaceIso_trans,
    iso_trans_targetIso]

/-- A specified isomorphism satisfying the evaluation square of a realized X map
induces a target isomorphism intertwining the evaluations. -/
theorem comp_targetEvaluation_of_evaluation_eq (e : M.pair ≅ Q.pair)
    (he : ∃ h, M.evaluation.compOfDefined F h =
      (surfaceIso e).hom.toRationalMap.comp Q.evaluation) :
    (surfaceIso (R.targetIso e)).hom.toRationalMap.comp Q.evaluation = P.evaluation := by
  obtain ⟨_, hR⟩ := R.evaluation_eq
  obtain ⟨_, he⟩ := he
  exact (R.comp_targetEvaluation_eq_iff e).mpr (he.symm.trans hR)

/-- The target isomorphism preserves a marked Picard class exactly when the
other isomorphism pulls that class back according to the realized isometry. -/
theorem pullback_picardMarking_targetIso_eq_iff (e : M.pair ≅ Q.pair) (a : L') :
    LineBundleClass.pullback (surfaceIso (R.targetIso e)).hom (Q.picardMarking a).toMul =
      (P.picardMarking a).toMul ↔
    M.picardMarking (I a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso e).hom (Q.picardMarking a).toMul) := by
  rw [R.picard_eq, ← (LineBundleClass.pullbackEquiv (surfaceIso R.iso)).injective.eq_iff,
    LineBundleClass.pullbackEquiv_apply, LineBundleClass.pullbackEquiv_apply,
    LineBundleClass.pullback_comp, ← Iso.trans_hom, ← MarkedSurface.surfaceIso_trans,
    iso_trans_targetIso, Additive.ofMul.injective.eq_iff, eq_comm]

/-- The target isomorphism fixes the ordered branches exactly when the other
isomorphism induces the realized dihedral action. -/
theorem boundaryCycleAction_targetIso_eq_one_iff (e : M.pair ≅ Q.pair) :
    letI : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
    letI : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
    letI : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
    (boundaryIso (R.targetIso e)).boundaryCycleAction P.cycle Q.cycle = 1 ↔
    (boundaryIso e).boundaryCycleAction M.cycle Q.cycle = g := by
  let : PrestableFamily (M.boundary ↘ Spec (.of k)) := M.prestable
  let : PrestableFamily (P.boundary ↘ Spec (.of k)) := P.prestable
  let : PrestableFamily (Q.boundary ↘ Spec (.of k)) := Q.prestable
  have hcomp : (boundaryIso e).boundaryCycleAction M.cycle Q.cycle =
      (boundaryIso (R.targetIso e)).boundaryCycleAction P.cycle Q.cycle * g := by
    simpa only [← MarkedSurface.boundaryIso_trans, iso_trans_targetIso, R.boundaryAction_eq]
      using (boundaryIso R.iso).boundaryCycleAction_trans M.cycle P.cycle
        (boundaryIso (R.targetIso e)) Q.cycle
  calc
    _ ↔ (boundaryIso (R.targetIso e)).boundaryCycleAction P.cycle Q.cycle * g = 1 * g :=
      (mul_left_inj g).symm
    _ ↔ _ := by rw [← hcomp, one_mul]

end QPainleve.SignedClusterModularGroup.FiberRealization
