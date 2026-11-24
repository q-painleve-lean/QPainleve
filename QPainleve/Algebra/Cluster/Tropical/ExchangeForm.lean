/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Order.Group.PiLex
public import QPainleve.Algebra.Cluster.Tropical.Basic
import QPainleve.Algebra.Cluster.ExchangeMatrix.Factorization

/-!
# Exchange forms under tropical evaluation

Evaluate a word on the standard basis of the lexicographically ordered exponent group.
The columns of the result pull back the initial exchange form to the terminal exchange
form with the sign of the word. Mutation uses the signed matrix factorization of
Berenstein and Zelevinsky, *Quantum cluster algebras*, §3. We use Tau Ceti's
`matrixMutationRight` with `Matrix.matrixMutation_eq_transpose_mul_right`. The sign of
the pivot exponent selects the factor by the tropical X formula of Gross, Hacking and
Keel, *Birational geometry of cluster algebras*, (1.4).
-/

public noncomputable section

open CategoryTheory Matrix Quiver TauCeti
open scoped Int Matrix

namespace QPainleve.Cluster

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]

local notation "columns" b:arg => Matrix.of (fun i j ↦ ofLex (b j) i)
local notation "row" => Function.Embedding.refl ι

private theorem columns_tropical_mutate_of_nonneg {B : SkewExchangeMatrix ι}
    (b : ι → Lex (ι → ℤ)) (p : ι) (hp : 0 ≤ b p) :
    columns ((Generator.mutate p).tropical B b) =
      columns b * matrixMutationRight row (-B.matrix) p 1 := by
  ext i j
  rw [mul_matrixMutationRight_apply]
  by_cases hj : j = p
  · subst j
    simp
    rfl
  · have hskew : B.matrix p j = -B.matrix j p := by
      simpa using B.isSkewSymmetrizer.mul_apply p j
    simp [Generator.tropical_mutate_of_ne_smul B b hj, hj, inf_eq_left.mpr hp,
      hskew, mul_comm]
    rfl

private theorem columns_tropical_mutate_of_nonpos {B : SkewExchangeMatrix ι}
    (b : ι → Lex (ι → ℤ)) (p : ι) (hp : b p ≤ 0) :
    columns ((Generator.mutate p).tropical B b) =
      columns b * matrixMutationRight row B.matrix p 1 := by
  have h := columns_tropical_mutate_of_nonneg (B := -B) (-b) p (by simpa using hp)
  simp only [Generator.tropical_neg, SkewExchangeMatrix.neg_matrix, neg_neg] at h
  -- Forget the lexicographic order to read negation as pointwise matrix negation.
  change -columns ((Generator.mutate p).tropical B b) =
    -columns b * matrixMutationRight row B.matrix p 1 at h
  rw [Matrix.neg_mul, neg_inj] at h
  exact h

private theorem exists_tropical_mutation_factor (B : SkewExchangeMatrix ι)
    (b : ι → Lex (ι → ℤ)) (p : ι) :
    ∃ F : Matrix ι ι ℤ, columns ((Generator.mutate p).tropical B b) = columns b * F ∧
      Fᵀ * B.matrix * F = (B.mutate p).matrix := by
  rcases le_total 0 (b p) with hp | hp
  · refine ⟨_, columns_tropical_mutate_of_nonneg b p hp, ?_⟩
    exact ((B.mutate_matrix p).trans
      (B.matrix.matrixMutation_eq_transpose_mul_right B.isSkewSymmetrizer p)).symm
  · refine ⟨_, columns_tropical_mutate_of_nonpos b p hp, ?_⟩
    have h := ((-B).mutate_matrix p).trans
      ((-B).matrix.matrixMutation_eq_transpose_mul_right (-B).isSkewSymmetrizer p)
    rw [B.mutate_neg, SkewExchangeMatrix.neg_matrix, SkewExchangeMatrix.neg_matrix,
      neg_neg, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
    exact h.symm

private theorem tropical_exchangeForm_step {B : SkewExchangeMatrix ι}
    (g : Generator ι) (b : ι → Lex (ι → ℤ)) (A : Matrix ι ι ℤ) (a : ℤ)
    (h : (columns b)ᵀ * A * columns b = a • B.matrix) :
    let P := columns (g.tropical B b)
    Pᵀ * A * P = (a * (-1) ^ g.inversionCount) • (g.target B).matrix := by
  dsimp only
  cases g with
  | mutate p =>
    obtain ⟨F, hF, hmut⟩ := exists_tropical_mutation_factor B b p
    rw [hF, transpose_mul]
    calc
      _ = Fᵀ * ((columns b)ᵀ * A * columns b) * F := by simp only [mul_assoc]
      _ = _ := by
        simp only [Generator.inversionCount_mutate, pow_zero, mul_one, Generator.target_mutate]
        rw [h, Matrix.mul_smul, Matrix.smul_mul, hmut]
  | permute σ =>
    have hP : columns ((Generator.permute σ).tropical B b) =
        (columns b).submatrix id σ := by
      ext i j
      simp
    have hA : (columns b)ᵀ.submatrix σ id * A =
        ((columns b)ᵀ * A).submatrix σ id := by
      simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
        Matrix.submatrix_mul_equiv (columns b)ᵀ A σ (Equiv.refl ι) id
    rw [hP, transpose_submatrix, hA]
    calc
      _ = ((columns b)ᵀ * A * columns b).submatrix σ σ :=
        Matrix.submatrix_mul_equiv _ _ σ (Equiv.refl ι) σ
      _ = _ := by
        rw [h]
        simp only [Generator.inversionCount_permute, pow_zero, mul_one,
          Generator.target_permute, SkewExchangeMatrix.reindex_matrix, Equiv.symm_symm]
        rfl
  | invert =>
    have hP : columns (Generator.invert.tropical B b) = -columns b := by
      ext i j
      rw [Matrix.of_apply, Generator.tropical_invert_apply]
      rfl
    simpa only [hP, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
      Generator.target_invert, SkewExchangeMatrix.neg_matrix, Generator.inversionCount_invert,
      pow_one, mul_neg, mul_one, neg_smul, smul_neg] using h

/-- For any signed word, tropical evaluation on the standard basis gives the
signed pullback relation between the source and target exchange matrices. -/
theorem _root_.Quiver.Path.tropical_exchangeForm {B C : SkewExchangeMatrix ι} (w : Word B C) :
    let b := Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := Lex (ι → ℤ)) ι)).map w)
      (fun i ↦ toLex (Pi.single i 1))
    let P := columns b
    Pᵀ * B.matrix * P = ((-1 : ℤ) ^ w.inversionCount) • C.matrix := by
  induction w with
  | nil =>
    have hP : columns (fun i ↦ toLex (Pi.single i 1 : ι → ℤ)) = (1 : Matrix ι ι ℤ) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply]
    simp only [Path.inversionCount_nil, Paths.lift_nil, SingleObj.id_as_one, Equiv.toFun_as_coe,
      Equiv.Perm.one_apply, pow_zero, one_smul, hP, transpose_one, one_mul, mul_one]
  | @cons C D w s ih =>
    simp only [Equiv.toFun_as_coe, tropical_map_cons_apply, Step.tropical_apply]
    rw [Path.inversionCount_cons, pow_add]
    simpa only [Step.target_eq s, Equiv.toFun_as_coe] using
      tropical_exchangeForm_step (Step.generator s) _ _ _ ih

end QPainleve.Cluster
