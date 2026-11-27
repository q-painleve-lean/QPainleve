/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Ray

import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Intersections of boundary rays of the projective plane

The three boundary rays are indexed by the two basis vectors and the negative of
their sum. Their Picard classes pair to one, including on the diagonal.
The off-diagonal calculation uses `Fan.classIntersectionNumber_rayBoundaryPoint`
and the diagonal uses `Fan.rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero`.
-/

public noncomputable section

open AlgebraicGeometry Module PointedCone
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "Φ" => projectiveSpace b hi
local notation "hΦ" => isRegular_projectiveSpace b hi
local notation "hc" => isComplete_projectiveSpace b hi

/-- Each ray divisor on the toric projective plane has self-intersection one. -/
@[simp]
theorem rayBoundarySelfIntersection_projectivePlane (ρ : (Φ).Ray) :
    (Φ).rayBoundarySelfIntersection hΦ ρ = 1 := by
  classical
  let e := projectivePlaneRayEquiv b hi
  let : Fintype (Φ).Ray := Fintype.ofEquiv _ e
  let : (Φ).algebraicRealization.IsProjectiveOver ℂ :=
    (Φ).isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have h := (Φ).rayBoundaryPoint_selfIntersection_smul_add_sum_eq_zero hΦ hdim ρ
  have hall : ∑ τ : (Φ).Ray, τ.primitiveGenerator = 0 := by
    rw [← Equiv.sum_comp e]
    simpa only [e, primitiveGenerator_projectivePlaneRayEquiv] using sum_projectiveSpaceGenerator b
  have hfilter : Finset.univ.filter (fun τ : (Φ).Ray ↦
      ρ ≠ τ ∧ ∃ σ : (Φ).cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) = Finset.univ.erase ρ := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨fun h ↦ h.1.symm, fun h ↦ ⟨h.symm, exists_cone_projectivePlane_of_ray_ne b hi h.symm⟩⟩
  dsimp only at h
  rw [hfilter, Finset.sum_erase_eq_sub (Finset.mem_univ ρ), hall, zero_sub,
    ← rayBoundarySelfIntersection_def, ← sub_eq_add_neg, sub_eq_zero] at h
  exact ρ.isPrimitiveGenerator.isPrimitive.zsmul_left_injective (h.trans (one_zsmul _).symm)

/-- Any two ray divisor classes on the toric projective plane have intersection one. -/
@[simp]
theorem classIntersectionNumber_projectivePlane_rayBoundaryPoint (ρ τ : (Φ).Ray) :
    let : Nonempty (Φ).cones := ⟨ρ.toCone⟩
    let := (Φ).uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    classIntersectionNumber ℂ (Φ).algebraicRealization
      (primeDivisorClass ((Φ).rayBoundaryPoint hΦ ρ))
      (primeDivisorClass ((Φ).rayBoundaryPoint hΦ τ)) = 1 := by
  intro _ _
  classical
  let : (Φ).algebraicRealization.IsProjectiveOver ℂ :=
    (Φ).isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
  by_cases h : ρ = τ
  · subst τ
    rw [← rayBoundarySelfIntersection_def, rayBoundarySelfIntersection_projectivePlane]
  · have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
    rw [(Φ).classIntersectionNumber_rayBoundaryPoint hΦ hdim h,
      ite_eq_left (exists_cone_projectivePlane_of_ray_ne b hi h)]

end TauCeti.Toric.Fan
