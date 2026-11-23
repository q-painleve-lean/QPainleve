/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization

/-!
# Congruence for skew-symmetric matrix mutation

For a skew-symmetric exchange matrix, the left mutation factor is the transpose of the right
factor, so the signed factorization gives a congruence.
-/

public section

namespace Matrix

open TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Mutation of a skew-symmetric exchange matrix is congruence by the positive-sign right
mutation factor of its negation. -/
theorem matrixMutation_eq_transpose_mul_right (ε : Matrix ι ι ℤ)
    (hε : ε.IsSkewSymmetrizer (fun _ ↦ 1)) (p : ι) :
    let F := matrixMutationRight (Function.Embedding.refl ι) (-ε) p 1
    matrixMutation (Function.Embedding.refl ι) ε p = Fᵀ * ε * F := by
  let row := Function.Embedding.refl ι
  let F := matrixMutationRight row (-ε) p 1
  have hF : Fᵀ = matrixMutationLeft row (-ε) p 1 := by
    ext i j
    have hpi : ε p i = -ε i p := by simpa using hε.mul_apply p i
    simp [F, row, matrixMutationRight_apply, matrixMutationLeft_apply, Matrix.one_apply,
      hpi, eq_comm]
  have h := matrixMutation_eq_mul row (-ε) p 1 (hε.neg.apply_self p) (Or.inl rfl)
  rw [matrixMutation_neg, Matrix.mul_neg, Matrix.neg_mul, ← hF] at h
  exact neg_injective h

end Matrix
