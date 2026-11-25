/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane

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

private theorem injective_projectivePlaneGenerator :
    Function.Injective (projectiveSpaceGenerator b) := by
  intro j k h
  rcases j with _ | j <;> rcases k with _ | k
  · rfl
  · have hh := congrArg (b.coord k) h
    fin_cases k <;> norm_num [Fin.sum_univ_two, Basis.coord_apply] at hh
  · have hh := congrArg (b.coord j) h
    fin_cases j <;> norm_num [Fin.sum_univ_two, Basis.coord_apply] at hh
  · exact congrArg some (b.injective (by simpa only [projectiveSpaceGenerator_some] using h))

/-- The two basis rays of the plane fan are indexed by `some` and their negative
sum is indexed by `none`. -/
def projectivePlaneRayEquiv : Option (Fin 2) ≃ (Φ).Ray :=
  ((Equiv.ofInjective _ (injective_projectivePlaneGenerator b)).trans
    (Set.equivOfEq (range_primitiveGenerator_projectiveSpace b hi).symm)).trans
      (Equiv.ofInjective _ Ray.primitiveGenerator_injective).symm

/-- A labelled ray has the corresponding primitive generator of the plane fan. -/
@[simp]
theorem primitiveGenerator_projectivePlaneRayEquiv (j : Option (Fin 2)) :
    (projectivePlaneRayEquiv b hi j).primitiveGenerator = projectiveSpaceGenerator b j := by
  exact congrArg Subtype.val
    ((Equiv.ofInjective _ Ray.primitiveGenerator_injective).apply_symm_apply _)

/-- Any two distinct rays of the plane fan belong to a common cone. -/
theorem exists_cone_projectivePlane_of_ray_ne {ρ τ : (Φ).Ray} (hne : ρ ≠ τ) :
    ∃ σ : (Φ).cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  classical
  let e := projectivePlaneRayEquiv b hi
  obtain ⟨a, rfl⟩ := e.surjective ρ
  obtain ⟨c, rfl⟩ := e.surjective τ
  have hn : a ≠ c := fun h ↦ hne (congrArg e h)
  have hs : ({a, c} : Set (Option (Fin 2))) ≠ Set.univ := by
    intro h
    have he := Set.ncard_pair hn
    rw [h, Set.ncard_univ] at he
    simp at he
  have hcone : projectiveSpaceCone b i {a, c} ∈ (Φ).cones :=
    (mem_projectiveSpace_cones b hi).mpr ⟨_, hs, rfl⟩
  have hle (j : Option (Fin 2)) (hj : j ∈ ({a, c} : Set (Option (Fin 2)))) :
      (e j).toCone.val ≤ projectiveSpaceCone b i {a, c} := by
    rw [Ray.toCone_eq_hull_primitiveGenerator, primitiveGenerator_projectivePlaneRayEquiv,
      projectiveSpaceCone_def]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr
      (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hj)))
  exact ⟨⟨_, hcone⟩, hle a (by simp), hle c (by simp)⟩

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
