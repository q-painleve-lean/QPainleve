/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import QPainleve.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.AlgebraicGeometry.Curves.DualGraph.Cycle
import Mathlib.Tactic.Abel

/-!
# Dihedral action on a cycle of curves

A symmetry of the cycle acts on its vertices and on its branches. The branch action is
faithful even for a loop or a two-edge cycle. Conversely, any branch permutation preserving
incidence with the vertices and edges comes from a unique dihedral symmetry.
The cycle and its symmetries use `TauCeti.DualGraph.cycle` and Mathlib's `DihedralGroup`.
-/

public section

open TauCeti

namespace DihedralGroup

variable {n : ℕ}

/-- The dihedral action on the branches of the numbered cycle. A branch is a pair
consisting of the edge index and its endpoint number. -/
def cycleBranchPerm : DihedralGroup n →* Equiv.Perm (ZMod n × Fin 2) where
  toFun
    | r i => Equiv.prodCongr (Equiv.addRight i) (.refl _)
    | sr i => Equiv.prodCongr (Equiv.subLeft (-i - 1)) Fin.revPerm
  map_one' := by
    rw [one_def]
    ext ⟨j, b⟩ <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> ext ⟨x, b⟩ <;>
      simp [Equiv.Perm.mul_apply] <;> abel

@[simp]
theorem cycleBranchPerm_r_apply (i j : ZMod n) (b : Fin 2) :
    cycleBranchPerm (r i) (j, b) = (j + i, b) :=
  (rfl)

@[simp]
theorem cycleBranchPerm_sr_apply (i j : ZMod n) (b : Fin 2) :
    cycleBranchPerm (sr i) (j, b) = (-i - 1 - j, b.rev) :=
  (rfl)

/-- The images of the branches distinguish all dihedral elements, including when
distinct symmetries induce the same vertex permutation. -/
theorem cycleBranchPerm_injective (n : ℕ) : Function.Injective (cycleBranchPerm (n := n)) := by
  rintro (i | i) (j | j) h <;>
    have he := Equiv.congr_fun h (0, 0) <;>
    simp only [cycleBranchPerm_r_apply, cycleBranchPerm_sr_apply, zero_add, sub_zero,
      Prod.mk.injEq] at he
  · exact congrArg r he.1
  · exact (by decide : (0 : Fin 2) ≠ (0 : Fin 2).rev) he.2 |>.elim
  · exact (by decide : (0 : Fin 2).rev ≠ (0 : Fin 2)) he.2 |>.elim
  · congr 1
    simpa only [sub_left_inj, neg_inj] using he.1

/-- The orientation character, with value `1` on rotations and `-1` on reflections. -/
def cycleOrientationSign : DihedralGroup n →* ℤˣ where
  toFun
    | r _ => 1
    | sr _ => -1
  map_one' := (rfl)
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]

@[simp]
theorem cycleOrientationSign_r (i : ZMod n) : cycleOrientationSign (r i) = 1 :=
  (rfl)

@[simp]
theorem cycleOrientationSign_sr (i : ZMod n) : cycleOrientationSign (sr i) = -1 :=
  (rfl)

/-- A dihedral vertex map is determined by its orientation and by where it sends vertex zero. -/
theorem cycleVertexPerm_apply (g : DihedralGroup n) (j : ZMod n) :
    cycleVertexPerm g j = (cycleOrientationSign g : ℤ) • j + cycleVertexPerm g 0 := by
  cases g <;> simp [sub_eq_add_neg, add_comm]

/-- An orientation-preserving cycle action is the rotation determined by the image
of vertex zero. This covers the cycles with one or two components. -/
theorem eq_r_iff_cycleVertexPerm_zero_eq {g : DihedralGroup n} {j : ZMod n}
    (h : cycleOrientationSign g = 1) :
    g = r j ↔ cycleVertexPerm g 0 = j := by
  cases g with
  | r i => simp
  | sr i =>
    rw [cycleOrientationSign_sr] at h
    exact (by decide : (-1 : ℤˣ) ≠ 1) h |>.elim

/-- A reflection exchanges the two ordered branches at every node. -/
theorem cycleBranchPerm_snd (g : DihedralGroup n) (j : ZMod n) (b : Fin 2) :
    (cycleBranchPerm g (j, b)).2 = if cycleOrientationSign g = -1 then b.rev else b := by
  have h : (1 : ℤˣ) ≠ -1 := by decide
  cases g <;> simp [h]

variable [NeZero n]

/-- The action on branches induces the action on vertices through the endpoint map. -/
@[simp]
theorem cycle_endpoint_cycleBranchPerm (g : DihedralGroup n) (j : ZMod n) (b : Fin 2) :
    (DualGraph.cycle n).endpoint (cycleBranchPerm g (j, b)).1 (cycleBranchPerm g (j, b)).2 =
      cycleVertexPerm g ((DualGraph.cycle n).endpoint j b) := by
  cases g <;> fin_cases b <;> simp [DualGraph.cycle] <;> abel

private theorem cycleBranchPerm_snd_eq_of_incidence
    (f : Equiv.Perm (ZMod n × Fin 2)) (e v : ZMod n → ZMod n)
    (he : ∀ j b, (f (j, b)).1 = e j)
    (hv : ∀ j b, (DualGraph.cycle n).endpoint (f (j, b)).1 (f (j, b)).2 =
      v ((DualGraph.cycle n).endpoint j b)) :
    ∀ j b, (f (j, b)).2 = if (f (0, 0)).2 = 0 then b else b.rev := by
  let p (j : ZMod n) (b : Fin 2) := (f (j, b)).2
  have hzero (j : ZMod n) : (if p j 0 = 0 then e j else e j + 1) = v j := by
    simpa [DualGraph.cycle, he, p] using hv j 0
  have hone (j : ZMod n) : (if p j 1 = 0 then e j else e j + 1) = v (j + 1) := by
    simpa [DualGraph.cycle, he, p] using hv j 1
  have hdiff (j : ZMod n) : p j 0 ≠ p j 1 := by
    intro h
    exact zero_ne_one (congrArg Prod.snd
      (f.injective (Prod.ext ((he j 0).trans (he j 1).symm) h)))
  -- The incoming and outgoing branches at a vertex remain distinct.
  have hstep (j : ZMod n) : p (j + 1) 0 ≠ p j 1 := by
    intro h
    have hv' := (hzero (j + 1)).trans (hone j).symm
    rw [h] at hv'
    have hidx : e (j + 1) = e j := by
      split at hv' <;> simpa only [add_left_inj] using hv'
    exact zero_ne_one (congrArg Prod.snd (f.injective
      (Prod.ext ((he (j + 1) 0).trans (hidx.trans (he j 1).symm)) h)))
  have hp (j : ZMod n) : p j 0 = p 0 0 := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective j
    induction m with
    | zero => simp only [Nat.cast_zero]
    | succ m ih =>
      rw [Nat.cast_succ, ← ih]
      have := hstep (m : ZMod n)
      have := hdiff (m : ZMod n)
      omega
  intro j b
  have hb : b = 0 ∨ b = 1 := by omega
  have hh := hdiff j
  have hj := hp j
  have hp₀ : (f (0, 0)).2 = p 0 0 := rfl
  rw [hp₀]
  rcases hb with rfl | rfl <;> by_cases h : p 0 0 = 0
  · simpa only [h, ↓reduceIte] using hj.trans h
  · simp only [h, ↓reduceIte]
    exact (by omega : p j 0 = 1).trans (rfl : 1 = (0 : Fin 2).rev)
  · simpa only [h, ↓reduceIte] using (by omega : p j 1 = 1)
  · simp only [h, ↓reduceIte]
    exact (by omega : p j 1 = 0).trans (rfl : 0 = (1 : Fin 2).rev)

private theorem cycleBranchPerm_exists_of_endpoint
    (f : Equiv.Perm (ZMod n × Fin 2)) (e v : ZMod n → ZMod n)
    (he : ∀ j b, (f (j, b)).1 = e j)
    (hv : ∀ j b, (DualGraph.cycle n).endpoint (f (j, b)).1 (f (j, b)).2 =
      v ((DualGraph.cycle n).endpoint j b)) :
    ∃ g : DihedralGroup n, cycleBranchPerm g = f := by
  have hbranch := cycleBranchPerm_snd_eq_of_incidence f e v he hv
  let s : ZMod n := if (f (0, 0)).2 = 0 then 1 else -1
  have hzero (j : ZMod n) : (if (f (0, 0)).2 = 0 then e j else e j + 1) = v j := by
    have h₀ := hv j 0
    rw [hbranch j 0] at h₀
    by_cases h : (f (0, 0)).2 = 0 <;> simpa [DualGraph.cycle, he, h] using h₀
  have hs (j : ZMod n) : v (j + 1) = v j + s := by
    have h₁ := hv j 1
    rw [hbranch j 1] at h₁
    rw [← hzero j]
    by_cases h : (f (0, 0)).2 = 0
    · simpa [DualGraph.cycle, he, s, h] using h₁.symm
    · have h' : e j = v (j + 1) := by
        simpa [DualGraph.cycle, he, h] using h₁
      simp [s, h, ← h', ← sub_eq_add_neg]
  have hvertex (j : ZMod n) : v j = v 0 + j * s := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective j
    induction m with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]
    | succ m ih => rw [Nat.cast_succ, hs, ih, add_mul, one_mul, add_assoc]
  by_cases h : (f (0, 0)).2 = 0
  · refine ⟨r (v 0), Equiv.ext fun ⟨j, b⟩ ↦ Prod.ext ?_ ?_⟩
    · have hh : e j = v j := by simpa [h] using hzero j
      rw [cycleBranchPerm_r_apply, he, hh, hvertex j]
      simp [s, h, add_comm]
    · simpa [h] using (hbranch j b).symm
  · refine ⟨sr (-v 0), Equiv.ext fun ⟨j, b⟩ ↦ Prod.ext ?_ ?_⟩
    · have hh : e j + 1 = v j := by simpa [h] using hzero j
      simp only [cycleBranchPerm_sr_apply, he, neg_neg]
      calc
        v 0 - 1 - j = v j - 1 := by
          rw [hvertex j]
          simp [s, h]
          abel
        _ = e j := by rw [← hh, add_sub_cancel_right]
    · simpa [h] using (hbranch j b).symm

/-- A branch permutation of a numbered cycle that respects both edge and vertex
incidence is induced by a unique element of the dihedral group. -/
theorem existsUnique_cycleBranchPerm
    (f : Equiv.Perm (ZMod n × Fin 2)) (e v : ZMod n → ZMod n)
    (he : ∀ j b, (f (j, b)).1 = e j)
    (hv : ∀ j b, (DualGraph.cycle n).endpoint (f (j, b)).1 (f (j, b)).2 =
      v ((DualGraph.cycle n).endpoint j b)) :
    ∃! g : DihedralGroup n, cycleBranchPerm g = f := by
  obtain ⟨g, hg⟩ := cycleBranchPerm_exists_of_endpoint f e v he hv
  exact ⟨g, hg, fun _ h ↦ cycleBranchPerm_injective n (h.trans hg.symm)⟩

end DihedralGroup
