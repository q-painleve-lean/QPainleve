/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Basic

/-!
# Primitive rays of the projective-space fan

The primitive ray generators of the fan of projective space are the vectors of
the chosen basis and the negative of their sum. This identifies the rays in the
native `Fan.projectiveSpace` with its defining family of lattice vectors.
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- For a positive-dimensional projective-space fan the prescribed lattice vectors are
exactly the primitive generators of the actual rays of the fan. -/
theorem range_primitiveGenerator_projectiveSpace [Fintype ι] [Nonempty ι]
    (b : Basis ι ℤ N) (hi : IsIntegralLattice i) :
    Set.range (Ray.primitiveGenerator (Phi := projectiveSpace b hi)) =
      Set.range (projectiveSpaceGenerator b) := by
  classical
  have hprim (k : Option ι) : IsPrimitive (projectiveSpaceGenerator b k) := by
    cases k with
    | some j => simpa only [projectiveSpaceGenerator_some] using b.isPrimitive j
    | none =>
      obtain ⟨j⟩ := ‹Nonempty ι›
      exact isPrimitive_def.mpr ⟨-b.coord j, by simp⟩
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨S, -, hS⟩ := (mem_projectiveSpace_cones b hi).mp r.toCone.property
    have hnonempty : S.Nonempty := Set.ne_empty_iff_nonempty.mp fun h ↦
      r.toCone_ne_bot _ (by rw [← hS, h, projectiveSpaceCone_empty])
    obtain ⟨k, hk⟩ := hnonempty
    have hm : i (projectiveSpaceGenerator b k) ∈ r.toCone.val := by
      rw [← hS, projectiveSpaceCone_def]
      exact subset_hull (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hk))
    exact ⟨k, (r.primitiveGenerator_eq_of_mem_of_isPrimitive hm (hprim k)).symm⟩
  · rintro ⟨k, rfl⟩
    let C := hull ℝ {i (projectiveSpaceGenerator b k)}
    have hC : C ∈ (projectiveSpace b hi).cones := (mem_projectiveSpace_cones b hi).mpr
      ⟨{k}, Set.singleton_ne_univ k,
        by rw [projectiveSpaceCone_def, Set.image_singleton, Set.image_singleton]⟩
    have hne : i (projectiveSpaceGenerator b k) ≠ 0 := by
      exact (map_ne_zero_iff i hi.injective).mpr (hprim k).ne_zero
    let r : (projectiveSpace b hi).Ray := ⟨⟨C, hC⟩, finrank_span_coe_hull_singleton hne⟩
    exact ⟨r, r.primitiveGenerator_eq_of_mem_of_isPrimitive
      (subset_hull (Set.mem_singleton _)) (hprim k)⟩

variable (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

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
noncomputable def projectivePlaneRayEquiv : Option (Fin 2) ≃ (projectiveSpace b hi).Ray :=
  ((Equiv.ofInjective _ (injective_projectivePlaneGenerator b)).trans
    (Set.equivOfEq (range_primitiveGenerator_projectiveSpace b hi).symm)).trans
      (Equiv.ofInjective _ Ray.primitiveGenerator_injective).symm

/-- A labelled ray has the corresponding primitive generator of the plane fan. -/
@[simp]
theorem primitiveGenerator_projectivePlaneRayEquiv (j : Option (Fin 2)) :
    (projectivePlaneRayEquiv b hi j).primitiveGenerator = projectiveSpaceGenerator b j := by
  exact congrArg Subtype.val
    ((Equiv.ofInjective _ Ray.primitiveGenerator_injective).apply_symm_apply _)

end TauCeti.Toric.Fan
