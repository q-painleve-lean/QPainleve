/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback
public import Mathlib.Algebra.Ring.Parity

import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Inversion normal form for signed cluster words

Negating both endpoint matrices commutes with each generator at the matrix level.
The corresponding edges intertwine simultaneous coordinate inversion. This allows inversions
to move to the beginning of a word and cancel in pairs. The resulting typed word has the
same pullback, and its initial inversion is present precisely when the original word has
odd inversion count.
-/

public section

namespace QPainleve.Cluster

open Quiver

variable {ι : Type*}

namespace Generator

/-- The contribution of a generator to a word's inversion count. -/
def inversionCount : Generator ι → ℕ
  | .mutate _ | .permute _ => 0
  | .invert => 1

@[simp]
theorem inversionCount_mutate (p : ι) : (mutate p).inversionCount = 0 :=
  (rfl)

@[simp]
theorem inversionCount_permute (σ : Equiv.Perm ι) : (permute σ).inversionCount = 0 :=
  (rfl)

@[simp]
theorem inversionCount_invert : (invert : Generator ι).inversionCount = 1 :=
  (rfl)

@[simp]
theorem inversionCount_eq_zero (g : Generator ι) : g.inversionCount = 0 ↔ g ≠ .invert := by
  cases g <;> simp

@[simp]
theorem inversionCount_reverse (g : Generator ι) : g.reverse.inversionCount = g.inversionCount := by
  cases g <;> simp

@[simp]
theorem inversionCount_reindex {κ : Type*} (g : Generator ι) (e : ι ≃ κ) :
    (g.reindex e).inversionCount = g.inversionCount := by
  cases g <;> simp

variable [DecidableEq ι]

/-- Applying a generator to the negated matrix negates its target as well. -/
@[simp]
theorem target_neg (g : Generator ι) (B : SkewExchangeMatrix ι) :
    g.target (-B) = -(g.target B) := by
  cases g <;> simp

end Generator

variable [DecidableEq ι] {B C : SkewExchangeMatrix ι}

namespace Step

/-- Apply the same generator between the negated exchange matrices. -/
def neg (s : Step B C) : Step (-B) (-C) :=
  ⟨s.generator, by rw [Generator.target_neg, s.target_eq]⟩

@[simp]
theorem neg_generator (s : Step B C) : s.neg.generator = s.generator :=
  (rfl)

/-- The inversion after an edge has the same pullback as inversion before the edge with
both endpoints negated. Both paths run from `B` to `-C`. -/
theorem xPullback_mul_xInversion (k : Type*) [Field k] (s : Step B C) :
    s.xPullback k * xInversion k ι = xInversion k ι * s.neg.xPullback k := by
  simp only [xPullback_eq, neg_generator, AlgEquiv.aut_mul]
  cases s.generator with
  | mutate p => simpa [Pi.neg_def] using
      (xMutation_trans_xInversion k p (fun i ↦ B.matrix i p)).symm
  | permute σ => simpa using xInversion_trans_xReindex k σ
  | invert => simp

end Step

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve.Cluster CategoryTheory

variable {ι : Type*} [DecidableEq ι] {B C D : SkewExchangeMatrix ι}

/-- Count the global inversions in a signed cluster word. -/
def inversionCount : ∀ {C : SkewExchangeMatrix ι}, Word B C → ℕ
  | _, .nil => 0
  | _, .cons w s => w.inversionCount + s.generator.inversionCount

@[simp]
theorem inversionCount_nil : (Path.nil : Word B B).inversionCount = 0 :=
  (rfl)

@[simp]
theorem inversionCount_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).inversionCount = w.inversionCount + (Step.generator s).inversionCount :=
  (rfl)

@[simp]
theorem inversionCount_toPath (s : B ⟶ C) :
    s.toPath.inversionCount = (Step.generator s).inversionCount := by
  simp [Hom.toPath]

/-- Concatenating words adds their inversion counts. -/
@[simp]
theorem inversionCount_comp (w : Word B C) (v : Word C D) :
    (w.comp v).inversionCount = w.inversionCount + v.inversionCount := by
  induction v with
  | nil => simp
  | cons _ _ ih => simp [ih, add_assoc]

/-- Reversal preserves the number of global inversions. -/
@[simp]
theorem inversionCount_reverse (w : Word B C) :
    w.reverse.inversionCount = w.inversionCount := by
  induction w with
  | nil => simp [Path.reverse]
  | cons _ _ ih => simp [Path.reverse, ih, add_comm]

/-- Changing the labels of a signed word preserves its inversion count. -/
@[simp]
theorem inversionCount_reindex {κ : Type*} [DecidableEq κ] (e : ι ≃ κ) (w : Word B C) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).inversionCount = w.inversionCount := by
  induction w with
  | nil => simp
  | cons _ _ ih => simp [ih]

variable (k : Type*) [Field k]

private def HasInversionNormalForm (w : Word B C) : Prop :=
  (Even w.inversionCount ∧ ∃ v : Word B C, v.inversionCount = 0 ∧ w.xPullback k = v.xPullback k) ∨
    (Odd w.inversionCount ∧ ∃ v : Word (-B) C,
      v.inversionCount = 0 ∧ w.xPullback k = xInversion k ι * v.xPullback k)

private theorem hasInversionNormalForm_toPath_comp (s : B ⟶ C) (w : Word C D)
    (h : HasInversionNormalForm k w) : HasInversionNormalForm k (s.toPath.comp w) := by
  by_cases hs : Step.generator s = Generator.invert
  · have hC : C = -B := by
      simpa [hs] using (Step.target_eq s).symm
    subst C
    have hp : Step.xPullback k s = xInversion k ι := by simp [Step.xPullback_eq, hs]
    rcases h with ⟨he, v, hv, h⟩ | ⟨ho, hh⟩
    · exact Or.inr ⟨by simpa [hs, add_comm] using he.add_odd odd_one, v, hv, by simp [hp, h]⟩
    · rw [SkewExchangeMatrix.neg_neg] at hh
      obtain ⟨v, hv, h⟩ := hh
      have hCancel : xInversion k ι * xInversion k ι = 1 := xInversion_trans_xInversion k ι
      exact Or.inl ⟨by simpa [hs, add_comm] using ho.add_odd odd_one, v, hv,
        by simp [hp, h, ← mul_assoc, hCancel]⟩
  · have hc : (Step.generator s).inversionCount = 0 :=
      (Generator.inversionCount_eq_zero _).2 hs
    rcases h with ⟨he, v, hv, h⟩ | ⟨ho, v, hv, h⟩
    · exact Or.inl ⟨by simpa [hc] using he, s.toPath.comp v, by simp [hc, hv], by simp [h]⟩
    · refine Or.inr ⟨by simpa [hc] using ho,
        (Hom.toPath (a := -B) (b := -C) (Step.neg s)).comp v, by simp [hc, hv], ?_⟩
      simp only [xPullback_comp, xPullback_toPath, h, ← mul_assoc, Step.xPullback_mul_xInversion]

private theorem hasInversionNormalForm (w : Word B C) : HasInversionNormalForm k w := by
  have hnil : HasInversionNormalForm k (Path.nil : Word C C) :=
    Or.inl ⟨by simp, Path.nil, inversionCount_nil, rfl⟩
  exact Paths.induction_fixed_target (b := (Paths.of _).obj C)
    (P := fun {_} v ↦ HasInversionNormalForm k v) hnil
    (fun v s h ↦ hasInversionNormalForm_toPath_comp k s v h) w

/-- A word with even inversion count has the same pullback as an inversion-free word
with the same endpoints. -/
theorem exists_xPullback_eq_of_even_inversionCount (w : Word B C) (h : Even w.inversionCount) :
    ∃ v : Word B C, v.inversionCount = 0 ∧ w.xPullback k = v.xPullback k := by
  rcases hasInversionNormalForm k w with h' | h'
  · exact h'.2
  · exact ((Nat.not_even_iff_odd.2 h'.1) h).elim

/-- A word with odd inversion count has the same pullback as an initial inversion followed
by an inversion-free word from the negated source matrix to the original target. -/
theorem exists_xPullback_eq_of_odd_inversionCount (w : Word B C) (h : Odd w.inversionCount) :
    ∃ v : Word (-B) C, v.inversionCount = 0 ∧ w.xPullback k = xInversion k ι * v.xPullback k := by
  rcases hasInversionNormalForm k w with h' | h'
  · exact ((Nat.not_odd_iff_even.2 h'.1) h).elim
  · exact h'.2

end Quiver.Path
