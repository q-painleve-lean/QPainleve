/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Chow.NodalIntersection
import QPainleve.AlgebraicGeometry.Curves.DualGraph.Cycle.Basic
import QPainleve.LinearAlgebra.BilinearForm.Cycle

/-!
# Nonnegative complexity of nodal boundary cycles

A nodal cycle on a smooth integral projective surface has at most two more components
than the Picard rank. The off-diagonal entries of the Picard intersection
matrix count the numbered nodes and give enough linearly independent classes.
The bound controls the number of fiber transformations in the ruled case of
[Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*,
Proposition 1.3](https://arxiv.org/html/1106.4977v3#S1.Thmproposition3).
-/

public section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A numbered nodal Cartier cycle on a smooth integral projective surface over an
algebraically closed field has nonnegative complexity when its Picard group
is finitely generated. -/
theorem boundaryComplexity_nonneg_of_nodalCycleNumbering
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [Module.Finite ℤ (Additive (LineBundleClass X))]
    (D : X.IdealSheafData) (hD : D.IsEffectiveCartier)
    [PrestableFamily (D.subscheme ↘ Spec (.of k))]
    {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
    {n : ℕ} [NeZero n] (A : NodalCycleNumbering p n) :
    0 ≤ D.boundaryComplexity := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x ↦
    letI := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) x
    inferInstance
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let u := A.boundaryPrimeEquiv hD
  let q := D.boundaryPrimeEmbedding ∘ u
  let c : ZMod n → Additive (LineBundleClass X) := fun j ↦
    Additive.ofMul (primeDivisorClass (q j))
  have hq (j : ZMod n) : (q j : X) ∈ D.support :=
    D.range_boundaryPrimeEmbedding.le ⟨u j, rfl⟩
  have hpair (i j : ZMod n) (hij : i ≠ j) :
      Chow.intersectionBilinForm k X (c i) (c j) =
        (if j = i + 1 then 1 else 0) + (if i = j + 1 then 1 else 0) := by
    rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul,
      Chow.classIntersectionNumber_eq_ncard_of_nodal hD
        PrestableFamily.atWorstNodalOfRelativeDimensionOne
        ((D.boundaryPrimeEmbedding.injective.comp u.injective).ne hij) (hq i) (hq j)]
    simp only [Function.comp_apply, coe_boundaryPrimeEmbedding]
    rw [A.closure_boundaryPrime_inter_of_ne hD hij,
      Set.ncard_image_of_injective _ A.ambientNode_injective,
      DualGraph.ncard_cycle_edges_of_ne i j hij]
    simp only [Nat.cast_add, apply_ite ((↑) : ℕ → ℤ), Nat.cast_zero, Nat.cast_one,
      eq_sub_iff_add_eq, (eq_comm : j + 1 = i ↔ i = j + 1)]
  have hli := (Chow.intersectionBilinForm k X).linearIndependent_cycle_segment c hpair
  have hrank := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hrank
  have hcard : D.boundaryPrimes.ncard = n := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr u, Nat.card_zmod]
  rw [D.boundaryComplexity_def, hcard]
  omega

end AlgebraicGeometry.Scheme.IdealSheafData
