/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import TauCeti.Data.ZMod.FinEquiv

/-!
# Order of representatives of a cyclic map

A map of finite cycles that increases by one at exactly one source edge per
target edge has its selected representatives in order when cut at a preimage
of zero.
-/

public section

namespace ZMod

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Suppose a map of cycles increases by one precisely at the edges in the image
of `retain` and is constant at the remaining edges. Then a chosen section
`survive` lists the representatives in strictly increasing order after rotating
the source to start at `survive 0`. -/
theorem strictMono_val_sub_of_succ_eq_add_ite
    (survive : ZMod n → ZMod m) (retain : ZMod n ↪ ZMod m) (a : ZMod m → ZMod n)
    (ha : ∀ j, a (survive j) = j)
    (hstep : ∀ j, a (j + 1) = a j + if j ∈ Set.range retain then (1 : ZMod n) else 0) :
    StrictMono fun j : Fin n ↦ (survive (ZMod.finEquiv n j) - survive 0).val := by
  classical
  let o := survive 0
  let steps := Finset.univ.image (fun j ↦ (retain j - o).val)
  let count (t : ℕ) := ∑ s ∈ Finset.range t, if s ∈ steps then (1 : ℕ) else 0
  have hc : steps.card = n := by
    rw [Finset.card_image_of_injective]
    · exact ZMod.card n
    · exact (ZMod.val_injective m).comp ((Equiv.subRight o).injective.comp retain.injective)
  have hmono : Monotone count := monotone_nat_of_le_succ fun t ↦ by
    dsimp only [count]
    rw [Finset.sum_range_succ]
    exact Nat.le_add_right _ _
  have hbound (t : ℕ) : count t ≤ n := by
    dsimp only [count]
    rw [Finset.sum_boole, ← hc]
    exact Finset.card_le_card fun j hj ↦ (Finset.mem_filter.mp hj).2
  have hstep' {t : ℕ} (ht : t < m) : t ∈ steps ↔ o + (t : ZMod m) ∈ Set.range retain := by
    simp only [steps, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    exact exists_congr fun j ↦ by
      have htval : (t : ZMod m).val = t := ZMod.val_natCast_of_lt ht
      conv_lhs => rw [← htval, (ZMod.val_injective m).eq_iff]
      rw [sub_eq_iff_eq_add, add_comm (t : ZMod m)]
  have hcount (t : ℕ) (ht : t ≤ m) : a (o + (t : ZMod m)) = (count t : ZMod n) := by
    induction t with
    | zero => simpa [count, o] using ha 0
    | succ t ih =>
      rw [Nat.cast_succ, ← add_assoc, hstep, ih (by omega)]
      dsimp only [count]
      rw [Finset.sum_range_succ, Nat.cast_add]
      simp only [← hstep' (t := t) (by omega)]
      split <;> simp
  have hval (j : ZMod n) : count (survive j - o).val = j.val := by
    by_cases hj : j = 0
    · simp [hj, o, count]
    have hcast : (count (survive j - o).val : ZMod n) = j := by
      rw [← hcount _ (ZMod.val_lt _).le, ZMod.natCast_zmod_val, add_sub_cancel, ha]
    have hlt := hbound (survive j - o).val
    rcases hlt.lt_or_eq with hlt | hEq
    · exact (ZMod.val_natCast_of_lt hlt).symm.trans (congrArg ZMod.val hcast)
    · rw [hEq, ZMod.natCast_self] at hcast
      exact (hj hcast.symm).elim
  intro j l hjl
  refine lt_of_not_ge fun h ↦ ?_
  have hle := hmono h
  rw [hval, hval] at hle
  have hvalFin (j : Fin n) : (ZMod.finEquiv n j).val = j.val := by
    rw [ZMod.finEquiv_apply, ZMod.val_natCast_of_lt j.isLt]
  simp only [hvalFin] at hle
  exact (not_le_of_gt hjl) hle

end ZMod
