/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Finset.Dedup

/-!
# Surviving cyclic ray indices

Removing a list of ray labels leaves a finite set of survivors in the original
numbering. `Finset.orderEmbOfFin` enumerates them starting from the least surviving label.
-/

public section

namespace TauCeti.Toric.Fan

variable {m : ℕ} [NeZero m] (l : List (ZMod m))

/-- The uncontracted ray indices in the original numbering. -/
def survivingRayIndices : Finset (Fin m) :=
  (l.toFinset.map (ZMod.finEquiv m).symm.toEquiv.toEmbedding)ᶜ

theorem survivingRayIndices_def :
    survivingRayIndices l = (l.toFinset.map (ZMod.finEquiv m).symm.toEquiv.toEmbedding)ᶜ :=
  (rfl)

@[simp]
theorem mem_survivingRayIndices (j : Fin m) :
    j ∈ survivingRayIndices l ↔ ZMod.finEquiv m j ∉ l := by
  simp [survivingRayIndices, Finset.mem_map_equiv]

/-- The number of survivors is the ray count minus the number of distinct removed rays. -/
theorem card_survivingRayIndices :
    (survivingRayIndices l).card = m - l.toFinset.card := by
  rw [survivingRayIndices, Finset.card_compl, Finset.card_map, Fintype.card_fin]

end TauCeti.Toric.Fan
