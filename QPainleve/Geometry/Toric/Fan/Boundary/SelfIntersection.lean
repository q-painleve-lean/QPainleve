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

/-- The self-intersection of the prime boundary divisor associated to a ray. -/
noncomputable def rayBoundarySelfIntersection (hΦ : Φ.IsRegular) (ρ : Φ.Ray) : ℤ :=
  letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
  letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let D := LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)
  classIntersectionNumber ℂ Φ.algebraicRealization D D

/-- The boundary self-intersection is computed in the native Picard intersection pairing. -/
theorem rayBoundarySelfIntersection_def (hΦ : Φ.IsRegular) (ρ : Φ.Ray) :
    letI : Nonempty Φ.cones := ⟨ρ.toCone⟩
    letI := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let D := LineBundleClass.primeDivisorClass (Φ.rayBoundaryPoint hΦ ρ)
    Φ.rayBoundarySelfIntersection hΦ ρ = classIntersectionNumber ℂ Φ.algebraicRealization D D :=
  (rfl)

private theorem relation_of_neighbors [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) {prev ρ next : Φ.Ray}
    (hne : prev ≠ next)
    (hneighbors : ∀ τ : Φ.Ray, (ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
      τ = prev ∨ τ = next) :
    prev.primitiveGenerator + Φ.rayBoundarySelfIntersection hΦ ρ • ρ.primitiveGenerator +
      next.primitiveGenerator = 0 := by
  classical
  let := Fintype.ofFinite Φ.Ray
  have hsum := Φ.rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero hΦ hN ρ
  have hfilter : Finset.univ.filter (fun τ : Φ.Ray ↦
      ρ ≠ τ ∧ ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) = {prev, next} := by
    ext τ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using hneighbors τ
  rw [hfilter, Finset.sum_pair hne] at hsum
  simpa only [rayBoundarySelfIntersection_def, add_left_comm, add_assoc] using hsum

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
  intro D
  obtain ⟨prev, next, hprev, hnext, hneighbors⟩ := exists_ray_neighbors b hΦ hc ρ
  have hne : prev ≠ next := by
    intro h
    rw [h] at hprev
    omega
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  refine ⟨prev, next, hprev, hnext, hneighbors, ?_⟩
  simpa only [rayBoundarySelfIntersection_def] using relation_of_neighbors hΦ hN hne hneighbors

/-- For a specified oriented pair of neighbours, the boundary self-intersection
determines the next primitive generator from the preceding two. -/
theorem primitiveGenerator_add_selfIntersection_smul_add_eq_zero
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {prev ρ next : Φ.Ray}
    (hprev : b.detDualEquiv prev.primitiveGenerator ρ.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, prev.toCone ≤ σ ∧ ρ.toCone ≤ σ)
    (hnext : b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ) :
    prev.primitiveGenerator + Φ.rayBoundarySelfIntersection hΦ ρ • ρ.primitiveGenerator +
      next.primitiveGenerator = 0 := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hprevDet : b.detDualEquiv ρ.primitiveGenerator prev.primitiveGenerator = -1 := by
    rw [b.detDualEquiv_swap, hprev.1]
  have hne : prev ≠ next := by
    intro h
    rw [h, hnext.1] at hprevDet
    omega
  exact relation_of_neighbors hΦ hN hne (ray_neighbors_iff_of_det b hΦ hc hprev hnext)

end TauCeti.Toric.Fan
