/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Hom.Basic

import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.FinRange

/-!
# Surviving cyclic ray indices

Removing a list of ray labels gives an increasing enumeration of the survivors
in the original cyclic numbering, starting from the least surviving label.
-/

public section

namespace TauCeti.Toric.Fan

variable {m : ℕ} [NeZero m] (l : List (ZMod m))

/-- Uncontracted ray indices in their original cyclic order beginning at the least index. -/
def survivingRayIndices : List (Fin m) :=
  (List.finRange m).filter fun j ↦ ZMod.finEquiv m j ∉ l

theorem survivingRayIndices_def :
    survivingRayIndices l = (List.finRange m).filter (fun j ↦ ZMod.finEquiv m j ∉ l) :=
  (rfl)

@[simp]
theorem mem_survivingRayIndices (j : Fin m) :
    j ∈ survivingRayIndices l ↔ ZMod.finEquiv m j ∉ l := by
  simp [survivingRayIndices]

/-- The ray selected by the index in the ordered list of survivors. -/
def survivingRayOrderEmbedding : Fin (survivingRayIndices l).length ↪o Fin m :=
  OrderEmbedding.ofStrictMono (survivingRayIndices l).get <|
    fun _ _ h ↦ List.pairwise_iff_get.mp
      ((List.pairwise_lt_finRange m).filter _) _ _ h

@[simp]
theorem survivingRayOrderEmbedding_apply (j : Fin (survivingRayIndices l).length) :
    survivingRayOrderEmbedding l j = (survivingRayIndices l).get j :=
  (rfl)

theorem mem_range_survivingRayOrderEmbedding (j : Fin m) :
    j ∈ Set.range (survivingRayOrderEmbedding l) ↔ ZMod.finEquiv m j ∉ l := by
  rw [← mem_survivingRayIndices, List.mem_iff_get]
  simp only [Set.mem_range, survivingRayOrderEmbedding_apply]

/-- The number of survivors is the ray count minus the number of distinct removed rays. -/
theorem length_survivingRayIndices :
    (survivingRayIndices l).length = m - l.toFinset.card := by
  classical
  let E := (ZMod.finEquiv m).symm.toEquiv.toEmbedding
  have hFinset : (survivingRayIndices l).toFinset = (l.toFinset.map E)ᶜ := by
    ext j
    simp [E, Finset.mem_map_equiv]
  have hn : (survivingRayIndices l).Nodup := (List.nodup_finRange m).filter _
  rw [← List.toFinset_card_of_nodup hn, hFinset, Finset.card_compl, Finset.card_map,
    Fintype.card_fin]

end TauCeti.Toric.Fan
