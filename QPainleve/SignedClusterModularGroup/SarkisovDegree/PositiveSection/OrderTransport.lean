/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Finset.Preimage
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence

import Mathlib.Order.Fin.Basic

/-!
# Transport of selected positive-section orders

When a resolved elementary link removes its pivot and inserts a reverse center
off the section, the largest remaining positive orders can be tracked without
recomputing the selection. Keeping the relative order of the retained stages
preserves priority among equal orders, including infinitely near centers.
-/

public section

open AlgebraicGeometry

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y X' Y' : Scheme} {n : ℕ}
  {T : BlowupTower X (n + 1) Y} {U : BlowupTower X' (1 + n) Y'}
  {D : X.IdealSheafData} {D' : X'.IdealSheafData}
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U)
  {j : Fin (n + 1)} {order : Fin (n + 1) → ℤ} {order' : Fin (1 + n) → ℤ}

/-- When the section loses one center and the reverse center lies off the
section, transport a selection containing the pivot to the largest remaining
orders. The new selection uses one fewer step and keeps the original priority
of earlier stages among equal orders. Its sum is the old selected sum less
the order removed at the pivot. -/
theorem largest_strictTransform_orders_of_corner_pivot
    (hsection : hU.strictTransformCoefficients D' =
      Fin.append (0 : Fin 1 → ℤ) (hT.strictTransformCoefficients D ∘ j.succAbove))
    (horder : ∀ l : Fin n, order' (l.natAdd 1) = order (j.succAbove l))
    {top : Finset (Fin (n + 1))} {k : ℕ} (hk : 0 < k) (hj : j ∈ top) :
    let sectionCenters := hT.strictTransformCenterIndices D
    let sectionCenters' := hU.strictTransformCenterIndices D'
    let positive := sectionCenters.filter (fun l ↦ 0 < order l)
    let positive' := sectionCenters'.filter (fun l ↦ 0 < order' l)
    let top' := (top.preimage j.succAbove (Fin.succAbove_right_injective (p := j)).injOn).map
      (Fin.natAddEmb 1)
    top ⊆ positive → top.card = min k positive.card →
    (∀ i ∈ top, ∀ l ∈ sectionCenters, l < i → order i ≤ order l → l ∈ top) →
    (∀ i ∈ top, ∀ l ∈ sectionCenters, l ∉ top → order l ≤ order i) →
    top' ⊆ positive' ∧ top'.card = min (k - 1) positive'.card ∧
      (∀ i ∈ top', ∀ l ∈ sectionCenters', l < i → order' i ≤ order' l → l ∈ top') ∧
      (∀ i ∈ top', ∀ l ∈ sectionCenters', l ∉ top' → order' l ≤ order' i) ∧
      (∑ l ∈ top', order' l) = (∑ l ∈ top, order l) - order j := by
  classical
  intro sectionCenters sectionCenters' positive positive' top' hsub hcard hpriority hlarge
  let tail (s : Finset (Fin (n + 1))) :=
    s.preimage j.succAbove (Fin.succAbove_right_injective (p := j)).injOn
  let e := Fin.natAddOrderEmb (m := n) 1
  have horder' (l : Fin n) : order' (e l) = order (j.succAbove l) := horder l
  have horderEmb (l : Fin n) : order' (e.toEmbedding l) = order (j.succAbove l) := horder l
  have hmap (s : Finset (Fin (n + 1))) : (tail s).map j.succAboveEmb = s.erase j := by
    rw [Finset.map_eq_image, Fin.coe_succAboveEmb]
    dsimp only [tail]
    rw [Finset.image_preimage]
    ext l
    simp [Fin.range_succAbove, and_comm]
  have hsection' : sectionCenters' = (tail sectionCenters).map e.toEmbedding := by
    dsimp only [sectionCenters']
    rw [hT.strictTransformCenterIndices_eq_map_of_coefficients_eq_append_zero hU _ hsection]
    apply congrArg (Finset.map (Fin.natAddEmb 1))
    ext l
    simp [tail, sectionCenters, Finset.mem_preimage]
  have hpositive' : positive' = (tail positive).map e.toEmbedding := by
    dsimp only [positive']
    rw [hsection', Finset.filter_map]
    apply congrArg (Finset.map e.toEmbedding)
    ext l
    simp [tail, positive, Finset.mem_preimage, horder']
  have htop' : top' = (tail top).map e.toEmbedding := rfl
  have hsub' := (Finset.map_subset_map (f := e.toEmbedding)).mpr (Finset.monotone_preimage
    (Fin.succAbove_right_injective (p := j)) hsub)
  refine ⟨hpositive'.symm ▸ hsub', ?_, ?_, ?_, ?_⟩
  · have hc (s : Finset (Fin (n + 1))) (hs : j ∈ s) :
        ((tail s).map e.toEmbedding).card + 1 = s.card := by
      rw [Finset.card_map, ← Finset.card_map j.succAboveEmb, hmap, Finset.card_erase_of_mem hs]
      exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨j, hs⟩)
    have htop := hc top hj
    have hpos := hc positive (hsub hj)
    rw [htop', hpositive']
    omega
  · intro a ha b hb hba hab
    rw [htop'] at ha ⊢
    rw [hsection'] at hb
    obtain ⟨a, haTail, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, hbTail, rfl⟩ := Finset.mem_map.mp hb
    exact (Finset.mem_map' e.toEmbedding).mpr (Finset.mem_preimage.mpr (hpriority _
      (Finset.mem_preimage.mp haTail) _ (Finset.mem_preimage.mp hbTail)
      (Fin.strictMono_succAbove j ((e.lt_iff_lt).mp hba)) (by simpa only [horderEmb] using hab)))
  · intro a ha b hb hbt
    rw [htop'] at ha hbt
    rw [hsection'] at hb
    obtain ⟨a, haTail, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, hbTail, rfl⟩ := Finset.mem_map.mp hb
    have hne : j.succAbove b ∉ top :=
      fun hb ↦ hbt ((Finset.mem_map' e.toEmbedding).mpr (Finset.mem_preimage.mpr hb))
    simpa only [horderEmb] using
      hlarge _ (Finset.mem_preimage.mp haTail) _ (Finset.mem_preimage.mp hbTail) hne
  · calc
      (∑ l ∈ (tail top).map e.toEmbedding, order' l) =
          ∑ l ∈ (tail top).map j.succAboveEmb, order l := by
        simp [Finset.sum_map, e, horder]
      _ = (∑ l ∈ top, order l) - order j := by
        rw [hmap, Finset.sum_erase_eq_sub hj]

end QPainleve.BlowupTower.IsClosedPointTower
