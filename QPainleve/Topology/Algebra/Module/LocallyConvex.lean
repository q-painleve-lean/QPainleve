/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Local convexity in finite-dimensional real vector spaces

A basis gives continuous linear coordinates on a finite-dimensional Hausdorff real
topological vector space. The coordinate topology is locally convex.
-/

public section

/-- A finite-dimensional Hausdorff real topological vector space is locally convex. -/
theorem locallyConvexSpace_of_finiteDimensional {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] : LocallyConvexSpace ℝ E := by
  let b := Module.finBasis ℝ E
  let e := b.equivFun.toContinuousLinearEquiv
  exact Topology.IsInducing.locallyConvexSpace (f := b.equivFun.toLinearMap)
    e.toHomeomorph.isInducing
