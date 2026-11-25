/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres

/-!
# First projected centers in concatenated blowup towers

A tail step is first over its point in the whole tower exactly when the
projected point avoids all prefix centers and the step is first in the tail.
-/

public section

open AlgebraicGeometry

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme} {m n : ℕ} {T : BlowupTower X m Y} {U : BlowupTower Y n Z}

/-- A tail step is first over its projected point in the concatenated tower
if and only if its projected point avoids the prefix centers and it is first
over its point in the tail. -/
theorem first_baseCenter_append_natAdd_iff
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U) (j : Fin n) :
    (∀ l < j.natAdd m, (hT.append hU).baseCenter l ≠
      (hT.append hU).baseCenter (j.natAdd m)) ↔
    T.toBase (hU.baseCenter j) ∉ Set.range hT.baseCenter ∧
      ∀ l < j, hU.baseCenter l ≠ hU.baseCenter j := by
  rw [baseCenter_append_natAdd hT hU, Fin.forall_fin_add]
  simp only [baseCenter_append_castAdd hT hU, baseCenter_append_natAdd hT hU,
    Fin.natAdd_lt_natAdd_iff]
  constructor
  · intro h
    refine ⟨?_, fun l hl he ↦ h.2 l hl (congrArg T.toBase he)⟩
    rintro ⟨l, hl⟩
    refine h.1 l ?_ hl
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rintro ⟨hj, h⟩
    refine ⟨fun l _ he ↦ hj ⟨l, he⟩, fun l hl he ↦ h l hl ?_⟩
    exact hT.injOn_toBase_compl_range_baseCenter
      (by simpa only [Set.mem_preimage, Set.mem_compl_iff, he] using hj) hj he

end QPainleve.BlowupTower.IsClosedPointTower
