/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback

/-!
# Commuting cluster X mutations

At two distinct labels with zero exchange entry between them, the two orders
of mutation induce the same pullback on the independent X coordinates.
-/

public section

namespace QPainleve.Cluster.Generator

variable {ι : Type*} [DecidableEq ι] (k : Type*) [Field k]

/-- Mutations across a zero exchange entry commute on the independent X function field.
In each product the second mutation uses the exchange matrix after the first mutation. -/
theorem xPullback_mutate_mul_mutate_comm (B : SkewExchangeMatrix ι) {p q : ι}
    (hpq : B.matrix p q = 0) :
    (mutate p).xPullback k B * (mutate q).xPullback k (B.mutate p) =
      (mutate q).xPullback k B * (mutate p).xPullback k (B.mutate q) := by
  rcases eq_or_ne p q with rfl | hne
  · rfl
  have hqp : B.matrix q p = 0 := by simp [B.apply_swap p q, hpq]
  have hp : (fun i ↦ (B.mutate q).matrix i p) = fun i ↦ B.matrix i p := by
    funext i
    rw [SkewExchangeMatrix.mutate_matrix]
    exact TauCeti.matrixMutation_apply_of_apply_row_eq_zero hne hqp i
  have hq : (fun i ↦ (B.mutate p).matrix i q) = fun i ↦ B.matrix i q := by
    funext i
    rw [SkewExchangeMatrix.mutate_matrix]
    exact TauCeti.matrixMutation_apply_of_apply_row_eq_zero hne.symm hpq i
  simp only [xPullback_mutate, hp, hq]
  have hfixp : xMutation k q (B.matrix · q) (xCoordinate k p) = xCoordinate k p := by
    simp [xMutation_apply_of_ne, hne, hpq]
  have hfixq : xMutation k p (B.matrix · p) (xCoordinate k q) = xCoordinate k q := by
    simp [xMutation_apply_of_ne, hne.symm, hqp]
  apply algEquiv_ext_xCoordinate k
  intro i
  simp only [AlgEquiv.mul_apply]
  by_cases hip : i = p
  · subst i
    simp [hfixp]
  by_cases hiq : i = q
  · subst i
    simp [hfixq]
  simp only [xMutation_apply_of_ne k q _ hiq, xMutation_apply_of_ne k p _ hip,
    map_mul, map_zpow₀, map_add, map_one, hfixp, hfixq]
  ring

end QPainleve.Cluster.Generator
