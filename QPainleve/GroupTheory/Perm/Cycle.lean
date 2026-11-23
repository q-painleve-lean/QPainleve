/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Numbering finite permutation cycles

A cyclic permutation on a finite type induces a numbering by a cyclic group with
the same cardinality. Choosing a starting point identifies the permutation with
addition by one.
-/

public section

namespace Equiv.Perm.IsCycleOn

/-- A permutation that is a single cycle on a finite type numbers its elements by
`ZMod` of the cardinality, starting at a specified point. Addition by one corresponds to
applying the permutation. -/
theorem exists_zmod_equiv {α : Type*} [Finite α] {p : Perm α} (hp : p.IsCycleOn _root_.Set.univ)
    (a₀ : α) : ∃ u : ZMod (Nat.card α) ≃ α, u 0 = a₀ ∧
      ∀ j, u (j + 1) = p (u j) := by
  classical
  let := Fintype.ofFinite α
  have : Nonempty α := ⟨a₀⟩
  let n := Nat.card α
  have hn : n = Fintype.card α := Nat.card_eq_fintype_card
  have : NeZero n := ⟨Nat.card_pos.ne'⟩
  have huniv : p.IsCycleOn (Finset.univ : Finset α) := by simpa using hp
  have hperiod (a b : ℕ) : (p ^ a) a₀ = (p ^ b) a₀ ↔ (a : ZMod n) = (b : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff, hn, ← Finset.card_univ (α := α)]
    exact huniv.pow_apply_eq_pow_apply (Finset.mem_univ a₀)
  let f (j : ZMod n) := (p ^ j.val) a₀
  have hf (a : ℕ) : f (a : ZMod n) = (p ^ a) a₀ :=
    (hperiod _ _).mpr (ZMod.natCast_zmod_val _)
  have hbij : Function.Bijective f := by
    constructor
    · intro j k h
      simpa only [ZMod.natCast_zmod_val] using (hperiod j.val k.val).mp h
    · intro b
      obtain ⟨a, _, ha⟩ := huniv.exists_pow_eq (Finset.mem_univ a₀) (Finset.mem_univ b)
      exact ⟨(a : ZMod n), (hf a).trans ha⟩
  let u := Equiv.ofBijective f hbij
  refine ⟨u, by simpa [u] using hf 0, ?_⟩
  intro j
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective j
  -- Evaluate the numbering on consecutive natural representatives.
  change f ((a : ZMod n) + 1) = p (f (a : ZMod n))
  rw [← Nat.cast_succ, hf, hf, pow_succ', Equiv.Perm.mul_apply]

end Equiv.Perm.IsCycleOn
