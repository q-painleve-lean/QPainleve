/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

/-!
# Stalks and orders of sums of ideal sheaves

The stalk of an arbitrary sum is the sum of the stalk ideals. Its order of vanishing
is the infimum of the orders of the summands.
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The stalk ideal of a sum is the sum of the stalk ideals. -/
@[simp]
theorem stalkIdeal_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkIdeal x = ⨆ i, (I i).stalkIdeal x := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (TopologicalSpace.Opens.mem_top x)
  simp only [stalkIdeal_eq_map _ ⟨U, hU⟩ x hxU, ideal_iSup, iSup_apply, Ideal.map_iSup]

/-- The order of a sum is the infimum of the orders of its summands. -/
@[simp]
theorem stalkOrder_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkOrder x = ⨅ i, (I i).stalkOrder x := by
  simp only [stalkOrder_def, stalkIdeal_iSup, Ideal.localOrder_iSup]

end AlgebraicGeometry.Scheme.IdealSheafData
