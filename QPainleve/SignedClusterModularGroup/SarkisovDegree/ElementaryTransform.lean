/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Prod.Lex.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Sarkisov bidegree under elementary transformation

The first coordinate is six times the degree, and the second is the sum of the
successive base orders. An elementary transformation keeps the fiber degree
and replaces one base order `m` by `b - m`. This preserves the homaloidal
identities and decreases the second coordinate when `2 * m > b`.

This is the fixed-degree decrease in Proposition 8.11 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open Prod.Lex

namespace QPainleve

variable {ι : Type*} [Fintype ι]

/-- The Sarkisov bidegree on a Hirzebruch surface, with fiber degree `b` and
total base order `M`. The degree coordinate is scaled by six. -/
def hirzebruchSarkisovBidegree (b M : ℕ) : ℕ ×ₗ ℕ := toLex (3 * b, M)

/-- Read the scaled fiber degree and total base order of a Hirzebruch bidegree. -/
@[simp]
theorem ofLex_hirzebruchSarkisovBidegree (b M : ℕ) :
    ofLex (hirzebruchSarkisovBidegree b M) = (3 * b, M) := (rfl)

variable {a b : ℤ} {m : ι → ℤ}

variable [DecidableEq ι]

/-- The total base order changes by `b - 2 * m j` when the pivot order is
replaced by the reverse-center order. -/
theorem sum_baseOrder_elementaryTransform (j : ι) :
    (∑ i, Function.update m j (b - m j) i) = (∑ i, m i) + b - 2 * m j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
    ← Finset.sum_erase_add Finset.univ m (Finset.mem_univ j)]
  ring

/-- An elementary transformation in a ruling of fiber degree `b` preserves both
homaloidal identities after replacing the selected multiplicity by `b - m j`.
For a center on the distinguished section, the new invariant is `e + 1`
and the fiber coefficient becomes `a + b - m j`. For a center off the section,
the transported section has parameter `e - 1` and coefficient `a - m j`.
Here `e` is the negative of the chosen section's square. -/
theorem homaloidal_identities_elementaryTransform {e : ℤ} (onSection : Bool) (j : ι)
    (hsq : ∑ i, m i ^ 2 = 2 * a * b - e * b ^ 2 - 1)
    (hsum : ∑ i, m i = 2 * a + (2 - e) * b - 3) :
    let a' := if onSection then a + b - m j else a - m j
    let e' := if onSection then e + 1 else e - 1
    let m' := Function.update m j (b - m j)
    (∑ i, m' i ^ 2 = 2 * a' * b - e' * b ^ 2 - 1) ∧
      (∑ i, m' i = 2 * a' + (2 - e') * b - 3) := by
  have hsq' : (∑ i, Function.update m j (b - m j) i ^ 2) =
      (∑ i, m i ^ 2) + ((b - m j) ^ 2 - m j ^ 2) := by
    simp_rw [Function.apply_update (fun _ (x : ℤ) ↦ x ^ 2) m j (b - m j)]
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
      ← Finset.sum_erase_add Finset.univ (fun i ↦ m i ^ 2) (Finset.mem_univ j)]
    ring
  cases onSection <;> dsimp only <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [hsq', sum_baseOrder_elementaryTransform, hsq, hsum] <;> constructor <;> ring

/-- At a center of order greater than half the fiber degree, an elementary
transformation strictly decreases the total base order at fixed degree. The
bound `m j ≤ b` makes the replacement a nonnegative order. -/
theorem hirzebruchSarkisovBidegree_elementaryTransform_lt (j : ι)
    (hm : ∀ i, 0 ≤ m i) (hmb : m j ≤ b) (hhigh : b < 2 * m j) :
    hirzebruchSarkisovBidegree b.toNat (∑ i, Function.update m j (b - m j) i).toNat <
      hirzebruchSarkisovBidegree b.toNat (∑ i, m i).toNat := by
  have hnew : 0 ≤ ∑ i, Function.update m j (b - m j) i := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i = j
    · simpa [hi] using sub_nonneg.mpr hmb
    · simpa [Function.update_of_ne hi] using hm i
  apply Prod.Lex.toLex_lt_toLex.mpr
  refine Or.inr ⟨rfl, ?_⟩
  have hsum := sum_baseOrder_elementaryTransform (m := m) (b := b) j
  omega

end QPainleve
