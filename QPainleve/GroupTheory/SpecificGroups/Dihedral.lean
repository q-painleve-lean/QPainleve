/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

import Mathlib.Tactic.Abel

/-!
# Dihedral action on cycle vertices

The dihedral group acts on the residue classes modulo the cycle length.
This action is faithful for cycles of length at least three.
-/

public section

namespace DihedralGroup

variable {n : ℕ}

/-- The dihedral action on the vertices of the numbered cycle. The reflection `sr i`
acts by `j ↦ -i - j`, in the multiplication convention of `DihedralGroup`. -/
def cycleVertexPerm : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun
    | r i => Equiv.addRight i
    | sr i => Equiv.subLeft (-i)
  map_one' := by
    rw [one_def]
    ext j
    simp
  map_mul' := by
    rintro (i | i) (j | j) <;> ext x <;>
      simp [Equiv.Perm.mul_apply] <;> abel

@[simp]
theorem cycleVertexPerm_r_apply (i j : ZMod n) :
    cycleVertexPerm (r i) j = j + i :=
  (rfl)

@[simp]
theorem cycleVertexPerm_sr_apply (i j : ZMod n) :
    cycleVertexPerm (sr i) j = -i - j :=
  (rfl)

/-- A cycle of length at least three distinguishes every rotation and reflection. -/
theorem cycleVertexPerm_injective (hn : 3 ≤ n) :
    Function.Injective (cycleVertexPerm (n := n)) := by
  let : Fact (2 < n) := ⟨hn⟩
  intro a b hab
  have h₀ := Equiv.congr_fun hab 0
  have h₁ := Equiv.congr_fun hab 1
  have hdiff := congrArg₂ (· - ·) h₁ h₀
  have hne := ZMod.neg_one_ne_one (n := n)
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg r (by simpa using h₀)
  · simp only [cycleVertexPerm_r_apply, cycleVertexPerm_sr_apply] at hdiff
    abel_nf at hdiff
    exact (hne (by simpa using hdiff.symm)).elim
  · simp only [cycleVertexPerm_r_apply, cycleVertexPerm_sr_apply] at hdiff
    abel_nf at hdiff
    exact (hne (by simpa using hdiff)).elim
  · exact congrArg sr (neg_injective (by simpa using h₀))

end DihedralGroup
