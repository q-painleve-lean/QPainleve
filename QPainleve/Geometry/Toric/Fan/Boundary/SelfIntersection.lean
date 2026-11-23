/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Adjacency
public import QPainleve.Geometry.Toric.Fan.Boundary.Intersection

/-!
# The boundary self-intersection recurrence of a toric surface

The primitive generators immediately before and after a ray satisfy an integral
linear relation with that ray. The coefficient of the middle ray is the self-intersection
of its boundary divisor. This is the wall relation of Fulton, *Introduction to Toric
Varieties*, §5.1, and determines the next generator from the preceding pair and the
self-intersection.
-/

public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry (LineBundleClass)
open TauCeti.AlgebraicGeometry.Chow

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- In a projective regular complete toric surface, the two oriented neighbours of a ray
satisfy the boundary self-intersection recurrence with its primitive generator. -/
theorem exists_rayBoundaryPoint_selfIntersection_relation
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let D := LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)
    ∃ prev next : Φ.Ray,
      b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1 ∧
      b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      (∀ τ : Φ.Ray, (ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
        τ = prev ∨ τ = next) ∧
      prev.primitiveGenerator +
        classIntersectionNumber ℂ Φ.algebraicRealization D D • ρ.primitiveGenerator +
        next.primitiveGenerator = 0 := by
  classical
  intro D
  let := Fintype.ofFinite Φ.Ray
  obtain ⟨prev, next, hprev, hnext, hneighbors⟩ := exists_ray_neighbors b hΦ hc ρ
  have hne : prev ≠ next := by
    intro h
    rw [h] at hprev
    omega
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hsum := Φ.rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero hΦ hN ρ
  have hfilter : Finset.univ.filter (fun τ : Φ.Ray ↦
      ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) = {prev, next} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hneighbors τ
  rw [hfilter, Finset.sum_pair hne] at hsum
  refine ⟨prev, next, hprev, hnext, hneighbors, ?_⟩
  simpa only [add_left_comm, add_assoc] using hsum

end TauCeti.Toric.Fan
