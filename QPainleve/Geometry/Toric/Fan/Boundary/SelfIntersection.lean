/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Adjacency
public import QPainleve.Geometry.Toric.Fan.Boundary.Intersection
public import QPainleve.Geometry.Toric.Fan.Picard.Presentation

/-!
# Boundary intersections and the self-intersection recurrence of a toric surface

The Picard intersection pairing on prime ray classes computes the degree of a ray
divisor from its coefficients at a ray and its two neighbours.

The primitive generators immediately before and after a ray satisfy an integral
linear relation with that ray. The coefficient of the middle ray is the self-intersection
of its boundary divisor. This is the wall relation of Fulton, *Introduction to Toric
Varieties*, §5.1, and determines the next generator from the preceding pair and the
self-intersection.
-/

public section

open AlgebraicGeometry Multiplicative
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

section Pairing

variable (Φ) [Nonempty Φ.cones] [decEq : DecidableEq Φ.Ray]
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ))]
  (hΦ : Φ.IsRegular)

local notation "B" => intersectionBilinForm ℂ Φ.algebraicRealization
local notation "R" => Φ.rayDivisorToPicard hΦ

open Classical in
/-- The Picard pairing of two prime ray classes is the boundary self-intersection on the
diagonal, and the indicator of a common cone off the diagonal. -/
theorem intersectionBilinForm_rayDivisorToPicard_single_single
    (hN : Module.finrank ℤ N = 2) (ρ τ : Φ.Ray) :
    B (R (Pi.single ρ 1)) (R (Pi.single τ 1)) =
      if ρ = τ then Φ.rayBoundarySelfIntersection hΦ ρ else
        if ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ then 1 else 0 := by
  simp only [intersectionBilinForm_apply, rayDivisorToPicard_single, one_smul, toMul_ofMul]
  by_cases h : ρ = τ
  · subst τ
    simp only [rayBoundarySelfIntersection_def, ite_true]
  · rw [ite_eq_right h]
    exact Φ.classIntersectionNumber_rayBoundaryPoint hΦ hN h

open Classical in
/-- The degree of a ray divisor along a prime boundary component is the sum of its
coefficients at the two oriented neighbours plus its coefficient at the component
times the boundary self-intersection. -/
theorem intersectionBilinForm_rayDivisorToPicard_single
    (b : Module.Basis (Fin 2) ℤ N) (hc : Φ.IsComplete) (a : Φ.Ray → ℤ) {prev ρ next : Φ.Ray}
    (hprev : b.detDualEquiv prev.primitiveGenerator ρ.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, prev.toCone ≤ σ ∧ ρ.toCone ≤ σ)
    (hnext : b.detDualEquiv ρ.primitiveGenerator next.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ next.toCone ≤ σ) :
    B (R (Pi.single ρ 1)) (R a) =
      a prev + Φ.rayBoundarySelfIntersection hΦ ρ * a ρ + a next := by
  let := Fintype.ofFinite Φ.Ray
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hne : prev ≠ next := by
    intro h
    have hd := hprev.1
    rw [h, b.detDualEquiv_swap, hnext.1] at hd
    omega
  have hneigh := ray_neighbors_iff_of_det b hΦ hc hprev hnext
  let adjacent (τ : Φ.Ray) := ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ
  have hfilter : (Finset.univ.erase ρ).filter adjacent = {prev, next} := by
    ext τ
    simpa only [adjacent, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_insert, Finset.mem_singleton, ne_comm (a := τ) (b := ρ)] using hneigh τ
  have hsum : R a = ∑ τ, a τ • R (Pi.single τ 1) := by
    conv_lhs => rw [← Finset.univ_sum_single a, map_sum]
    simp only [← map_zsmul, ← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ)]
  have hoff : ∑ τ ∈ Finset.univ.erase ρ, B (R (Pi.single ρ 1)) (a τ • R (Pi.single τ 1)) =
      a prev + a next := by
    rw [← Finset.sum_pair hne, ← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [map_zsmul, Φ.intersectionBilinForm_rayDivisorToPicard_single_single hΦ hN,
      ite_eq_right (Finset.ne_of_mem_erase hτ).symm]
    by_cases h : adjacent τ <;> simp [adjacent] at h ⊢
  rw [hoff, map_zsmul, Φ.intersectionBilinForm_rayDivisorToPicard_single_single hΦ hN,
    ite_eq_left rfl, Int.zsmul_eq_mul, mul_comm (a ρ)]
  abel

end Pairing

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
