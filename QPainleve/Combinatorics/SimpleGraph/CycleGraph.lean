/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import QPainleve.GroupTheory.SpecificGroups.Dihedral

import Mathlib.Tactic.Abel
import TauCeti.Combinatorics.SimpleGraph.CycleGraph

/-!
# Dihedral symmetries of cycle graphs

The dihedral group acts on the residue classes modulo the cycle length. For a cycle
of length at least three this action is faithful, and every graph automorphism has
this form. A permutation sending every consecutive pair to neighbors is determined
by its values at zero and one.
-/

public section

namespace SimpleGraph

variable {n : ℕ} [NeZero n]

/-- The neighbors of a residue class in the cycle graph are its predecessor and successor. -/
theorem cycleGraph_adj_finEquiv_symm (hn : 2 ≤ n) (x y : ZMod n) :
    (cycleGraph n).Adj ((ZMod.finEquiv n).symm x) ((ZMod.finEquiv n).symm y) ↔
      y = x + 1 ∨ y = x - 1 := by
  constructor
  · intro h
    rcases TauCeti.eq_add_one_or_eq_add_one_of_cycleGraph_adj h with h | h
    · exact Or.inl (by simpa only [map_add, map_one, RingEquiv.apply_symm_apply]
        using (congrArg (ZMod.finEquiv n) h))
    · exact Or.inr (eq_sub_iff_add_eq.mpr (by
        simpa only [map_add, map_one, RingEquiv.apply_symm_apply]
          using (congrArg (ZMod.finEquiv n) h.symm)))
  · intro h
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    obtain rfl : n = m + 2 := hm.trans (Nat.add_comm 2 m)
    rw [← mem_neighborSet, cycleGraph_neighborSet]
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
      ← map_one ((ZMod.finEquiv (m + 2)).symm), ← map_sub, ← map_add,
      EmbeddingLike.apply_eq_iff_eq, or_comm] using h

private theorem perm_eq_of_map_cycle_successors (hn : 3 ≤ n)
    {f g : Equiv.Perm (ZMod n)}
    (hf : ∀ x, f (x + 1) = f x + 1 ∨ f (x + 1) = f x - 1)
    (hg : ∀ x, g (x + 1) = g x + 1 ∨ g (x + 1) = g x - 1)
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1) : f = g := by
  let : Fact (2 < n) := ⟨hn⟩
  have hne (x : ZMod n) : x + 1 + 1 ≠ x := by
    intro h
    apply ZMod.neg_one_ne_one (n := n)
    calc
      -1 = x + 1 - (x + 1 + 1) := by abel
      _ = 1 := by rw [h]; abel
  have step (x : ZMod n) (hx : f x = g x) (hy : f (x + 1) = g (x + 1)) :
      f (x + 1 + 1) = g (x + 1 + 1) := by
    have hfne := f.injective.ne (hne x)
    have hgne := g.injective.ne (hne x)
    rcases hf x with h | h <;>
      rcases hf (x + 1) with hff | hff <;>
      rcases hg (x + 1) with hgg | hgg <;> grind
  ext x
  have aux (m : ℕ) : f (m : ZMod n) = g m ∧ f ((m : ZMod n) + 1) = g (m + 1) := by
    induction m with
    | zero => simpa using And.intro h₀ h₁
    | succ m ih =>
      simpa only [Nat.cast_succ] using And.intro ih.2 (step m ih.1 ih.2)
  simpa using (aux x.val).1

/-- A permutation of a cycle's residue classes that takes consecutive pairs to
neighbors is induced by a unique dihedral element when the cycle has length at least three. -/
theorem _root_.Equiv.Perm.existsUnique_dihedral_of_map_successors (f : Equiv.Perm (ZMod n))
    (hn : 3 ≤ n)
    (hf : ∀ x, f (x + 1) = f x + 1 ∨ f (x + 1) = f x - 1) :
    ∃! d : DihedralGroup n, DihedralGroup.cycleVertexPerm d = f := by
  have h₁ : f 1 = f 0 + 1 ∨ f 1 = f 0 - 1 := by simpa using hf 0
  have hex : ∃ d : DihedralGroup n, DihedralGroup.cycleVertexPerm d = f := by
    rcases h₁ with h | h
    · refine ⟨DihedralGroup.r (f 0), perm_eq_of_map_cycle_successors hn ?_ hf (by simp) ?_⟩
      · intro x
        exact Or.inl (by simp; abel)
      · simpa [add_comm] using h.symm
    · refine ⟨DihedralGroup.sr (-f 0),
        perm_eq_of_map_cycle_successors hn ?_ hf (by simp) ?_⟩
      · intro x
        exact Or.inr (by simp; abel)
      · rw [DihedralGroup.cycleVertexPerm_sr_apply, h]
        abel
  obtain ⟨d, hd⟩ := hex
  exact ⟨d, hd, fun e he ↦ DihedralGroup.cycleVertexPerm_injective hn (he.trans hd.symm)⟩

/-- Every automorphism of the cycle graph on at least three vertices acts by a unique
rotation or reflection on the residue classes. -/
theorem cycleGraph_existsUnique_dihedral (hn : 3 ≤ n) (f : cycleGraph n ≃g cycleGraph n) :
    ∃! d : DihedralGroup n, ∀ x : ZMod n,
      DihedralGroup.cycleVertexPerm d x = ZMod.finEquiv n (f ((ZMod.finEquiv n).symm x)) := by
  let e := ZMod.finEquiv n
  let p : Equiv.Perm (ZMod n) := e.toEquiv.permCongr f.toEquiv
  have hp (x : ZMod n) : p x = e (f (e.symm x)) := rfl
  have h := p.existsUnique_dihedral_of_map_successors hn (fun x ↦ by
    apply (cycleGraph_adj_finEquiv_symm (by omega) (p x) (p (x + 1))).mp
    simp only [hp, e, RingEquiv.symm_apply_apply]
    exact f.map_rel_iff.mpr ((cycleGraph_adj_finEquiv_symm (by omega) x (x + 1)).mpr
      (Or.inl rfl)))
  obtain ⟨d, hd, huniq⟩ := h
  exact ⟨d, fun x ↦ (Equiv.congr_fun hd x).trans (hp x),
    fun d' hd' ↦ huniq d' (Equiv.ext fun x ↦ (hd' x).trans (hp x).symm)⟩

end SimpleGraph
