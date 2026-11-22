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

variable [DecidableEq ι] {B C : SkewExchangeMatrix ι}

namespace Step

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
