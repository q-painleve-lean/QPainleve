/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Basic

/-!
# Comparing geometric realizations on source charts

The fixed-center evaluation squares of two realizations turn agreement of their
target evaluations into agreement of the two X maps on a dominant source chart.
This computes the rational compositions on their defined domains.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace QPainleve.SignedClusterModularGroup.FiberRealization

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L L' : Type u} [AddCommGroup L] [AddCommGroup L']
  {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
  {X X' W : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [X'.IsSeparated] [IsIntegral W]
  {M : MarkedSurface k n B X} {N N' : MarkedSurface k n B' X'}
  {F G : X ⤏ X'} {I J : B'.IsometryEquiv B} {g h : DihedralGroup n}

open MarkedSurface (surfaceIso)

/-- If two fixed-center realizations yield the same target evaluation on their
common source surface, the induced rational compositions agree on every
dominant chart of that source. -/
theorem exists_compOfDefined_eq_of_target_evaluation_eq
    (R : FiberRealization M N F I g) (R' : FiberRealization M N' G J h)
    (i : W ⟶ M.surface) [IsDominant i]
    (heq : (surfaceIso R.iso).hom.toRationalMap.comp N.evaluation =
      (surfaceIso R'.iso).hom.toRationalMap.comp N'.evaluation) :
    let e := i.toRationalMap.comp M.evaluation
    let x := e.fromFunctionField (IsLocalRing.closedPoint W.functionField)
    ∃ (hf : x ∈ F.domain) (hg : x ∈ G.domain),
      e.compOfDefined F hf = e.compOfDefined G hg := by
  obtain ⟨hf, hF⟩ := R.evaluation_eq
  obtain ⟨hg, hG⟩ := R'.evaluation_eq
  obtain ⟨hf', heF⟩ := i.toRationalMap.comp_compOfDefined M.evaluation F hf
  obtain ⟨hg', heG⟩ := i.toRationalMap.comp_compOfDefined M.evaluation G hg
  have h := congrArg (i.toRationalMap.comp ·) (hF.trans (heq.trans hG.symm))
  exact ⟨hf', hg', heF.trans (h.trans heG.symm)⟩

end QPainleve.SignedClusterModularGroup.FiberRealization
