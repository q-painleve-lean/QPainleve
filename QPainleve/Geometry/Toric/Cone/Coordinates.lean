/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

import TauCeti.Geometry.Convex.Cone.Face.Simplicial
import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Coordinates in regular cones

An extending basis gives a pointwise description of a regular cone by
nonnegative ray coordinates and vanishing complementary coordinates.
-/

public section

open Module PointedCone

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

namespace IsExtendingBasis

/-- A point belongs to the cone exactly when its coordinates in the extended real basis
are nonnegative and vanish away from the ray indices. -/
theorem mem_iff_real_basis_repr {σ : PointedCone ℝ V} {n : ℕ} {b : Basis (Fin n) ℤ N}
    {r : ToricRay σ ↪ Fin n} (hb : IsExtendingBasis i b r) (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (x : V) :
    x ∈ σ ↔ ∀ j, 0 ≤ (hi.isBaseChange.basis b).repr x j ∧
      (j ∉ Set.range r → (hi.isBaseChange.basis b).repr x j = 0) := by
  let c := hi.isBaseChange.basis b
  have hgen : (c : Fin n → V) ∘ r = i ∘ primitiveGenerator hi hσ := by
    funext ρ
    exact (hi.isBaseChange.basis_apply b (r ρ)).trans
      (congrArg i ((hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hi hσ))
  have hcone : hull ℝ (c '' Set.range r) = σ := by
    rw [← Set.range_comp, hgen, Set.range_comp, hσ.hull_primitiveGenerator hi]
  rw [← show x ∈ hull ℝ (c '' Set.range r) ↔ x ∈ σ by rw [hcone],
    mem_hull_image_iff_linearCombination]
  constructor
  · rintro ⟨a, ha, hp, rfl⟩ j
    rw [c.repr_linearCombination]
    exact ⟨hp j, fun hn ↦ Finsupp.notMem_support_iff.mp
      (fun hm ↦ hn ((Finsupp.mem_supported _ _).mp ha hm))⟩
  · intro h
    exact ⟨c.repr x, Finsupp.mem_supported _ _ |>.mpr (fun j hj ↦ by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hj) ((h j).2 hn)), fun j ↦ (h j).1,
      c.linearCombination_repr x⟩

/-- For a lattice point, the nonnegativity and support conditions of an extending basis
can be checked on its integral coordinates. -/
theorem mem_iff_lattice_basis_repr {σ : PointedCone ℝ V} {n : ℕ} {b : Basis (Fin n) ℤ N}
    {r : ToricRay σ ↪ Fin n} (hb : IsExtendingBasis i b r) (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (x : N) :
    i x ∈ σ ↔ ∀ j, 0 ≤ b.repr x j ∧ (j ∉ Set.range r → b.repr x j = 0) := by
  rw [hb.mem_iff_real_basis_repr hi hσ]
  apply forall_congr'
  intro j
  have he : (hi.isBaseChange.basis b).repr (i x) j = (b.repr x j : ℝ) :=
    hi.isBaseChange.basis_repr_comp_apply b x j
  rw [he]
  simp

end IsExtendingBasis

end TauCeti.Toric
