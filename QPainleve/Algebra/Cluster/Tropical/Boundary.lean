/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Algebra.Cluster.XMutation.Evaluation
public import QPainleve.Geometry.Toric.Fan.Boundary.Binomial

/-!
# Tropical mutation at toric boundary points

When X coordinates are specialized to torus characters times nonzero constants, the
orders of the mutated coordinates along a toric boundary ray are given by integer
Y-seed mutation. The chart evaluation only inverts the pivot binomial. Its order
formula includes the case where the pivot character has order zero. This is the
boundary tropicalization of the mutation in Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, (1.4).
-/

public noncomputable section

open AlgebraicGeometry Multiplicative TauCeti.Toric

namespace QPainleve.Cluster

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {ι : Type*} [DecidableEq ι]
  (Φ : Fan i) [Nonempty Φ.cones]

local notation "K" => Φ.algebraicRealization.functionField

/-- Specializing the X mutation chart to scaled characters gives a unique evaluation.
The orders of the mutated coordinates are the tropical mutation of the character pairings
with the ray generator. -/
theorem existsUnique_xMutationChartEval_toric_ord (hΦ : Φ.IsRegular) (ρ : Φ.Ray)
    (B : SkewExchangeMatrix ι) (p : ι) (c : ι → ℂˣ) (m : ι → N →+ ℤ) (hm : m p ≠ 0) :
    ∃! f : XMutationChart ℂ p →ₐ[ℂ] K,
      (∀ j, f (xMutationChartUnitX ℂ p j : XMutationChart ℂ p) =
        algebraMap ℂ K (c j : ℂ) * Φ.character (ofAdd (m j))) ∧
      ∀ j, Φ.algebraicRealization.ord
        (f (xMutationChartEquiv ℂ p (fun j ↦ B.matrix j p)
          (xMutationChartUnitX ℂ p j : XMutationChart ℂ p))) (Φ.rayBoundaryPoint hΦ ρ).val =
        (Generator.mutate p).tropical B (fun j ↦ m j ρ.primitiveGenerator) j := by
  let x (j : ι) : Kˣ := Units.map (algebraMap ℂ K).toMonoidHom (c j) *
    Φ.character.toHomUnits (ofAdd (m j))
  have hx (j : ι) : (x j : K) = algebraMap ℂ K (c j : ℂ) * Φ.character (ofAdd (m j)) := by
    simp [x]
  obtain ⟨hne, hbin⟩ := Φ.ord_rayBoundaryPoint_one_add_mul_character hΦ ρ (c p) hm
  rw [← hx p] at hne hbin
  let f := xMutationChartEval (R := ℂ) p x hne.isUnit
  have hf (j : ι) : f (xMutationChartUnitX ℂ p j : XMutationChart ℂ p) = x j :=
    by simp [f]
  have horder (j : ι) : Φ.algebraicRealization.ord (x j : K)
      (Φ.rayBoundaryPoint hΦ ρ).val = m j ρ.primitiveGenerator := by
    rw [hx, Φ.ord_rayBoundaryPoint_mul_character]
  refine ⟨f, ⟨fun j ↦ (hf j).trans (hx j), ?_⟩, ?_⟩
  · intro j
    let toUnits := Units.map (f : XMutationChart ℂ p →* K)
    by_cases hj : j = p
    · subst j
      have h := congrArg toUnits (map_xMutationChartUnitX_self ℂ p (fun j ↦ B.matrix j p))
      rw [map_inv] at h
      have he := congrArg Units.val h
      simp only [Units.val_inv_eq_inv_val, toUnits, Units.coe_map, MonoidHom.coe_ofClass, hf] at he
      rw [he, Scheme.ord_inv, horder, Generator.tropical_mutate_self]
    · have h := congrArg toUnits (map_xMutationChartUnitX_of_ne ℂ p (fun j ↦ B.matrix j p) hj)
      simp only [map_mul, map_zpow] at h
      have he := congrArg Units.val h
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, toUnits, Units.coe_map,
        MonoidHom.coe_ofClass, val_xMutationChartBinomial, map_add, map_one, hf] at he
      have hp := zpow_ne_zero (max (B.matrix j p) 0) (x p).ne_zero
      rw [he, Scheme.ord_mul (mul_ne_zero (x j).ne_zero hp) (zpow_ne_zero _ hne),
        Scheme.ord_mul (x j).ne_zero hp, Scheme.ord_zpow, Scheme.ord_zpow,
        horder, horder, hbin, Generator.tropical_mutate_of_ne B _ hj]
      simp [posPart_def, sub_eq_add_neg]
  · intro g hg
    apply Localization.algHom_ext
    apply TauCeti.LaurentRing.algHom_ext
    intro j
    simpa only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply,
      val_xMutationChartUnitX] using (hg.1 j).trans ((hf j).trans (hx j)).symm

end QPainleve.Cluster
