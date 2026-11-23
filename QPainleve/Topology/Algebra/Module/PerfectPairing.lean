/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Topology.Algebra.Module.PerfectPairing

import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous perfect pairings in finite dimensions

In a finite-dimensional Hausdorff topological vector space over a complete normed field,
every linear functional is continuous. A perfect pairing between such spaces therefore
identifies both spaces with the respective continuous duals.
-/

public section

namespace LinearMap

section

variable {R E F : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]
  {p : E →ₗ[R] F →ₗ[R] R}

/-- The left adjoint of a continuous perfect pairing separates points. -/
theorem IsContPerfPair.separatingLeft (hp : p.IsContPerfPair) : p.SeparatingLeft := by
  intro x hx
  apply hp.bijective_left.injective
  ext y
  simp [hx y]

/-- A continuous perfect pairing is nondegenerate as an algebraic pairing. -/
theorem IsContPerfPair.nondegenerate (hp : p.IsContPerfPair) : p.Nondegenerate := by
  let : p.IsContPerfPair := hp
  have hflip : p.flip.IsContPerfPair := inferInstance
  exact ⟨hp.separatingLeft, LinearMap.flip_separatingLeft.mp hflip.separatingLeft⟩

end

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

/-- An algebraically perfect pairing of Hausdorff topological vector spaces is continuously
perfect when one space is finite-dimensional. -/
theorem IsPerfPair.isContPerfPair {p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hp : p.IsPerfPair) :
    p.IsContPerfPair := by
  have : FiniteDimensional 𝕜 F := FiniteDimensional.of_injective p.flip hp.bijective_right.injective
  let : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
  let : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional
  exact
    { continuous_uncurry := IsModuleTopology.continuous_bilinear_of_finite_left p
      bijective_left := LinearMap.toContinuousLinearMap.bijective.comp hp.bijective_left
      bijective_right := LinearMap.toContinuousLinearMap.bijective.comp hp.bijective_right }

/-- In finite dimensions, a nondegenerate bilinear pairing between Hausdorff topological
vector spaces identifies each space with the continuous dual of the other. -/
theorem Nondegenerate.isContPerfPair {p : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hp : p.Nondegenerate) :
    p.IsContPerfPair :=
  (IsPerfPair.of_injective (ker_eq_bot.mp (separatingLeft_iff_ker_eq_bot.mp hp.1))
    (ker_eq_bot.mp (separatingRight_iff_flip_ker_eq_bot.mp hp.2))).isContPerfPair

end LinearMap
