/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Symmetry
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word

/-!
# Pullback along cluster X mutation words

A list of mutation directions determines an algebra automorphism of the field of independent
X coordinates. Each step uses the corresponding row of the current exchange matrix.
Pullback reverses concatenation, takes reversal to inversion at the mutated matrix, and
commutes with relabeling.
-/

public noncomputable section

open TauCeti

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι : Type*} [DecidableEq ι]

local notation "XField" => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

/-- Pullback along a list of mutation directions for a native square exchange matrix. Each
pullback uses the row of the current matrix and acts after the pullback of the tail. -/
def xMutationWord (B : ExchangeMatrix (Function.Embedding.refl ι)) : List ι → XField ≃ₐ[k] XField
  | [] => AlgEquiv.refl
  | p :: w => (xMutationWord (B.mutation p) w).trans (xMutation k p (fun i ↦ B.matrix p i))

@[simp]
theorem xMutationWord_nil (B : ExchangeMatrix (Function.Embedding.refl ι)) :
    xMutationWord k B [] = AlgEquiv.refl := (rfl)

@[simp]
theorem xMutationWord_cons (B : ExchangeMatrix (Function.Embedding.refl ι)) (p : ι) (w : List ι) :
    xMutationWord k B (p :: w) =
      (xMutationWord k (B.mutation p) w).trans (xMutation k p (fun i ↦ B.matrix p i)) := (rfl)

/-- A singleton mutation word has the elementary mutation pullback. -/
theorem xMutationWord_singleton (B : ExchangeMatrix (Function.Embedding.refl ι)) (p : ι) :
    xMutationWord k B [p] = xMutation k p (fun i ↦ B.matrix p i) := by
  ext x
  simp

/-- Pullback reverses the order of concatenation. The second word starts at the matrix
obtained after the first word. -/
theorem xMutationWord_append (B : ExchangeMatrix (Function.Embedding.refl ι)) (u v : List ι) :
    xMutationWord k B (u ++ v) =
      (xMutationWord k (B.mutationWord u) v).trans (xMutationWord k B u) := by
  induction u generalizing B with
  | nil => ext x; simp
  | cons p u ih => ext x; simp [ih]

/-- The pullback of a reversed word is the inverse pullback, based at the mutated matrix. -/
theorem xMutationWord_reverse (B : ExchangeMatrix (Function.Embedding.refl ι)) (w : List ι) :
    xMutationWord k (B.mutationWord w) w.reverse = (xMutationWord k B w).symm := by
  induction w generalizing B with
  | nil => simp
  | cons p w ih =>
    ext x
    simp [xMutationWord_append, ih, Pi.neg_def]

/-- Relabeling a native mutation word also relabels its pullback. The equivalence `e` sends
old labels to new labels, so the coordinate pullback uses `e.symm`. -/
theorem xMutationWord_trans_xReindex {κ : Type*} [DecidableEq κ] (e : ι ≃ κ)
    (B : ExchangeMatrix (Function.Embedding.refl ι)) (w : List ι) :
    (xMutationWord k (ExchangeMatrix.reindex (row' := Function.Embedding.refl κ)
      e e (by simp) B) (w.map e)).trans (xReindex k e.symm) =
      (xReindex k e.symm).trans (xMutationWord k B w) := by
  induction w generalizing B with
  | nil => ext x; simp
  | cons p w ih =>
    let B' := ExchangeMatrix.reindex (row' := Function.Embedding.refl κ) e e (by simp)
      (B.mutation p)
    have hstep := B.mutation_reindex (row' := Function.Embedding.refl κ) e e (by simp) p
    have hrow := xMutation_trans_xReindex k e.symm (e p) (fun i ↦ B.matrix p i)
    ext x
    simp only [List.map_cons, xMutationWord_cons, hstep, ExchangeMatrix.reindex_matrix,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, AlgEquiv.trans_apply]
    have htail := DFunLike.congr_fun (ih (B.mutation p)) x
    simp only [AlgEquiv.trans_apply] at htail
    rw [← htail]
    simpa only [AlgEquiv.trans_apply, Equiv.symm_apply_apply, Function.comp_def] using
      DFunLike.congr_fun hrow (xMutationWord k B' (w.map e) x)

end QPainleve.Cluster
