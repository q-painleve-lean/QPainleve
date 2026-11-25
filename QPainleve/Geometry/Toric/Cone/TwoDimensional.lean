/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Two-dimensional regular cones

The two primitive ray generators of a full regular cone give an integral basis
in rank two. They generate the cone, and their sum is the sum of the basis
vectors.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace IsRegularCone

/-- The two primitive ray generators of a full regular cone form an integral basis. -/
theorem exists_basis_primitiveGenerators {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i) (hN : Module.finrank ℤ N = 2)
    (hc : Nat.card (ToricRay σ) = 2) :
    ∃ (e : Fin 2 ≃ ToricRay σ) (b : Module.Basis (Fin 2) ℤ N),
      ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j) := by
  have := ToricRay.finite_of_fg hσ.fg
  let := Fintype.ofFinite (ToricRay σ)
  let e := (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hc)).symm
  obtain ⟨l, b₀, hb₀⟩ := hσ.exists_basis_sum
  have hl := Module.finrank_eq_nat_card_basis b₀
  rw [hN, Nat.card_sum, hc, Nat.card_fin] at hl
  have hl₀ : l = 0 := by omega
  subst l
  let q := (Equiv.sumEmpty (ToricRay σ) (Fin 0)).trans e.symm
  refine ⟨e, b₀.reindex q, fun j ↦ ?_⟩
  simpa [q] using (hb₀ (e j)).eq_primitiveGenerator hi hσ.toIsToricCone

/-- The cone hull of a basis of primitive ray generators is the original cone. -/
theorem hull_eq_of_basis_primitiveGenerators {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) :
    PointedCone.hull ℝ (i '' Set.range b) = σ := by
  have he : (b : Fin 2 → N) = primitiveGenerator hi hσ.toIsToricCone ∘ e := funext hb
  rw [he, e.surjective.range_comp, hσ.toIsToricCone.hull_primitiveGenerator hi]

/-- A two-ray regular cone in a rank-two lattice spans the ambient real vector space. -/
theorem span_eq_top_of_card_toricRay_eq_two {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i) (hN : Module.finrank ℤ N = 2)
    (hc : Nat.card (ToricRay σ) = 2) : Submodule.span ℝ (σ : Set V) = ⊤ := by
  obtain ⟨e, b, hb⟩ := hσ.exists_basis_primitiveGenerators hi hN hc
  let d := hi.isBaseChange.basis b
  have hd : Set.range d = i '' Set.range b := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext (hi.isBaseChange.basis_apply b))
  have hsub : Set.range d ⊆ (σ : Set V) := by
    rw [hd, ← hσ.hull_eq_of_basis_primitiveGenerators hi b e hb]
    exact PointedCone.subset_hull
  exact top_unique (d.span_eq ▸ Submodule.span_mono hsub)

/-- The sum of the generators of a two-ray cone is the sum of the two basis vectors. -/
theorem sum_primitiveGenerator_allRays {σ : PointedCone ℝ V}
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) (e : Fin 2 ≃ ToricRay σ)
    (hb : ∀ j, b j = primitiveGenerator hi hσ.toIsToricCone (e j)) :
    ∑ ρ ∈ ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) hσ.fg,
      primitiveGenerator hi hσ.toIsToricCone ρ = b 0 + b 1 := by
  classical
  let := Fintype.ofEquiv _ e
  have hall :
      ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) hσ.fg = Finset.univ := by
    ext ρ
    simp [ToricRay.mem_faceFinset, ρ.val.isFaceOf.le]
  rw [hall, ← Equiv.sum_comp e, Fin.sum_univ_two, ← hb 0, ← hb 1]

end IsRegularCone

namespace Fan

/-- A cone with two rays is nonzero. -/
theorem ne_bot_of_card_toricRay_eq_two {σ : PointedCone ℝ V}
    (hc : Nat.card (ToricRay σ) = 2) : σ ≠ ⊥ := by
  intro h
  have hz : Nat.card (ToricRay (⊥ : PointedCone ℝ V)) = 0 := Nat.card_eq_zero.mpr
    (Or.inl inferInstance)
  rw [h, hz] at hc
  omega

end Fan

end TauCeti.Toric
