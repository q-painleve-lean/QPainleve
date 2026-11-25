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
When a new center is prepended, a first center can also be selected with a
prescribed image and bounds on its order.
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

/-- Select a first center with the same image under the given morphisms after
prepending a center of order `β`. Over the new center's image, take the new
center. Over every other image, retain the original center and its order. -/
theorem exists_retained_first_center
    {X X' Y Y' W : Scheme} {n : ℕ} {T : BlowupTower X n Y} {U : BlowupTower X' (1 + n) Y'}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U)
    (f : X ⟶ W) (f' : X' ⟶ W) (p : X)
    (x : Fin n → ℤ) (y : Fin (1 + n) → ℤ) (β : ℤ)
    (hOrders : y = Fin.addCases (fun _ : Fin 1 ↦ -β) x)
    (hhead : f' (hU.baseCenter 0) = f p)
    (htail : ∀ j, f' (hU.baseCenter (j.natAdd 1)) = f (hT.baseCenter j))
    (hfirst : ∀ j : Fin n, hU.baseCenter (j.natAdd 1) ≠ hU.baseCenter 0 →
      (∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) →
      ∀ l < j.natAdd 1, hU.baseCenter l ≠ hU.baseCenter (j.natAdd 1))
    (j : Fin n) (hj : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) (hbound : -x j ≤ β) :
    ∃ l : Fin (1 + n), (∀ t < l, hU.baseCenter t ≠ hU.baseCenter l) ∧
      f' (hU.baseCenter l) = f (hT.baseCenter j) ∧ -x j ≤ -y l ∧ -y l ≤ β ∧
      (f (hT.baseCenter j) = f p → l = 0) ∧
      (f (hT.baseCenter j) ≠ f p → l = j.natAdd 1 ∧ y l = x j) := by
  by_cases heq : f (hT.baseCenter j) = f p
  · have hl : -y 0 = β := by
      have hzero : (0 : Fin (1 + n)) = Fin.castAdd n (0 : Fin 1) := rfl
      simp only [hOrders, hzero, Fin.addCases_left, neg_neg]
    exact ⟨0, fun t ht ↦ (Fin.not_lt_zero t ht).elim, hhead.trans heq.symm,
      hl ▸ hbound, hl.le, fun _ ↦ rfl, fun hn ↦ (hn heq).elim⟩
  · have hne : hU.baseCenter (j.natAdd 1) ≠ hU.baseCenter 0 :=
      fun h ↦ heq ((htail j).symm.trans ((congrArg f' h).trans hhead))
    have hl : y (j.natAdd 1) = x j := by simp only [hOrders, Fin.addCases_right]
    exact ⟨j.natAdd 1, hfirst j hne hj, htail j, by rw [hl], hl.symm ▸ hbound,
      fun h ↦ (heq h).elim, fun _ ↦ ⟨rfl, hl⟩⟩

end QPainleve.BlowupTower.IsClosedPointTower
