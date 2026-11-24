/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic

/-!
# Edges of a numbered cycle

The edge labelled `e` joins vertices `e` and `e + 1`. Counting the edges between
distinct vertices includes both parallel edges of the two-vertex cycle.
-/

public section

namespace TauCeti.DualGraph

variable {n : ℕ}

/-- The edges between distinct vertices of the numbered cycle count the two cyclic
adjacencies separately. In a two-vertex cycle both terms contribute. -/
theorem ncard_cycle_edges_of_ne (i j : ZMod n) (hij : i ≠ j) :
    ({e | (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)} : Set (ZMod n)).ncard =
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  have hprev : i = j + 1 ↔ j = i - 1 := eq_comm.trans eq_sub_iff_add_eq.symm
  simp only [hprev]
  by_cases hs : j = i + 1
  · by_cases ht : j = i - 1
    · simp only [eq_true hs, eq_true ht, and_true, ite_true, Set.ofPred_or,
        Set.ofPred_eq_eq_singleton, Set.singleton_union, Set.ncard_pair hij]
    · simp only [eq_true hs, eq_false ht, and_true, and_false, or_false, ite_true, ite_false,
        Set.ofPred_eq_eq_singleton, Set.ncard_singleton, add_zero]
  · by_cases ht : j = i - 1
    · simp only [eq_false hs, eq_true ht, and_true, and_false, false_or, ite_true, ite_false,
        Set.ofPred_eq_eq_singleton, Set.ncard_singleton, zero_add]
    · simp only [eq_false hs, eq_false ht, and_false, or_self, ite_false, Set.ofPred_false,
        Set.ncard_empty, add_zero]

end TauCeti.DualGraph
