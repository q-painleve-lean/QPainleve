/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Group.Submonoid.Operations

/-!
# Additive irreducibles in positively graded monoids

A positive natural-valued degree lets every nonzero element decompose into
additive irreducibles by induction on its degree.
-/

public section

namespace AddMonoidHom

variable {M : Type*} [AddCommMonoid M]
/-- A degree that is positive on nonzero elements ensures generation by additive
irreducibles. -/
theorem closure_setOf_addIrreducible_eq_top (d : M →+ ℕ) (hd : ∀ m, d m = 0 → m = 0) :
    AddSubmonoid.closure {m : M | AddIrreducible m} = ⊤ := by
  apply eq_top_iff.mpr
  intro m hmTop
  clear hmTop
  generalize hn : d m = n
  induction n using Nat.strong_induction_on generalizing m with
  | ind n ih =>
    by_cases hm : m = 0
    · exact hm ▸ zero_mem _
    by_cases hirr : AddIrreducible m
    · exact AddSubmonoid.subset_closure hirr
    simp only [addIrreducible_iff, not_and] at hirr
    push Not at hirr
    obtain ⟨a, b, rfl, ha, hb⟩ := hirr fun h ↦ hm (hd _ (Nat.isAddUnit_iff.mp (h.map d)))
    have ha' : d a ≠ 0 := fun h ↦ ha (hd _ h ▸ isAddUnit_zero)
    have hb' : d b ≠ 0 := fun h ↦ hb (hd _ h ▸ isAddUnit_zero)
    rw [map_add] at hn
    exact add_mem (ih (d a) (by omega) rfl) (ih (d b) (by omega) rfl)

end AddMonoidHom
