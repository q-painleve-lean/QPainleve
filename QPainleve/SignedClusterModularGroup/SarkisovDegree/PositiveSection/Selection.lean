/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Fin.Basic

import Mathlib.Data.Finset.Preimage

/-!
# Selection of successive positive-section pivots

The degree estimate for positive-section preparation uses the sum of the orders selected
on the original resolving tower. A pivot removes the earliest stage of maximal order.
The other section stages keep their order when the tower is reindexed, and the reverse
center is off the new positive section. The remaining selection therefore still consists
of the largest orders, and subtracting their sum from the current fiber coefficient gives
the same integer throughout preparation.
-/

public section

namespace QPainleve

variable {ι ι' κ : Type*} [LinearOrder ι] [LinearOrder ι'] [LinearOrder κ]

/-- A selection of up to `steps` stages from the positive-order section stages `s`.
Larger base orders take priority, with earlier stages taking priority in a tie. -/
structure IsPositiveSectionSelection (s : Finset ι) (order : ι → ℤ) (steps : ℕ)
    (selected : Finset ι) : Prop where
  /-- The selected stages belong to the section. -/
  subset : selected ⊆ s
  /-- The selection fills all the available slots up to the number of section stages. -/
  card_eq : selected.card = min steps s.card
  /-- An earlier stage of at least the same order has priority over a selected stage. -/
  mem_of_lt_of_le : ∀ i ∈ selected, ∀ j ∈ s, j < i → order i ≤ order j → j ∈ selected
  /-- All unselected stages have order bounded by each selected order. -/
  order_le : ∀ i ∈ selected, ∀ j ∈ s, j ∉ selected → order j ≤ order i

namespace IsPositiveSectionSelection

variable {s selected : Finset ι} {order : ι → ℤ} {steps : ℕ}

/-- With no positive section stages, the selection is empty for any number of steps. -/
@[simp]
theorem empty_iff : IsPositiveSectionSelection ∅ order steps selected ↔ selected = ∅ := by
  refine ⟨fun h ↦ Finset.subset_empty.mp h.subset, ?_⟩
  rintro rfl
  exact ⟨Finset.Subset.rfl, by simp, by simp, by simp⟩

/-- If no further pivot is required, the selection is empty. -/
@[simp]
theorem zero_iff : IsPositiveSectionSelection s order 0 selected ↔ selected = ∅ := by
  refine ⟨fun h ↦ Finset.card_eq_zero.mp (by simpa using h.card_eq), ?_⟩
  rintro rfl
  exact ⟨Finset.empty_subset _, by simp, by simp, by simp⟩

/-- The earliest stage of maximal order belongs to every selection with a positive slot count. -/
theorem mem_of_earliest_max (h : IsPositiveSectionSelection s order (steps + 1) selected)
    {p : ι} (hp : p ∈ s) (hmax : ∀ i ∈ s, order i ≤ order p)
    (hearly : ∀ i ∈ s, i < p → order i < order p) : p ∈ selected := by
  by_contra hmissing
  have hcard : 0 < selected.card := by
    rw [h.card_eq]
    exact lt_min (Nat.zero_lt_succ _) (Finset.card_pos.mpr ⟨p, hp⟩)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  have heq := le_antisymm (hmax i (h.subset hi)) (h.order_le i hi p hp hmissing)
  have hpi : p < i := lt_of_le_of_ne (le_of_not_gt fun hlt ↦
    (hearly i (h.subset hi) hlt).ne heq) (fun hpi ↦ hmissing (hpi ▸ hi))
  exact hmissing (h.mem_of_lt_of_le i hi p hp hpi heq.le)

/-- Removing one selected stage leaves a selection for one fewer step. -/
theorem erase (h : IsPositiveSectionSelection s order (steps + 1) selected)
    {p : ι} (hp : p ∈ selected) :
    IsPositiveSectionSelection (s.erase p) order steps (selected.erase p) where
  subset := Finset.erase_subset_erase _ h.subset
  card_eq := by
    rw [Finset.card_erase_of_mem hp, Finset.card_erase_of_mem (h.subset hp), h.card_eq]
    omega
  mem_of_lt_of_le := by
    intro i hi j hj hji hle
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨hne, h.mem_of_lt_of_le i (Finset.mem_of_mem_erase hi) j hjs hji hle⟩
  order_le := by
    intro i hi j hj hj'
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    exact h.order_le i (Finset.mem_of_mem_erase hi) j hjs
      (fun hmem ↦ hj' (Finset.mem_erase.mpr ⟨hne, hmem⟩))

/-- An increasing reindexing preserves the selection when it preserves the section orders. -/
theorem map_iff (e : κ ↪o ι) (s selected : Finset κ) (order' : κ → ℤ)
    (horder : ∀ i ∈ s, order (e i) = order' i) :
    IsPositiveSectionSelection (s.map e.toEmbedding) order steps (selected.map e.toEmbedding) ↔
      IsPositiveSectionSelection s order' steps selected := by
  constructor
  · intro h
    have hsub : selected ⊆ s := Finset.map_subset_map.mp h.subset
    refine ⟨hsub, by simpa only [Finset.card_map] using h.card_eq, ?_, ?_⟩
    · intro i hi j hj hji hle
      apply (Finset.mem_map' e.toEmbedding).mp
      refine h.mem_of_lt_of_le _ (Finset.mem_map_of_mem _ hi) _ (Finset.mem_map_of_mem _ hj)
        (e.strictMono hji) ?_
      simpa only [RelEmbedding.coe_toEmbedding, horder i (hsub hi), horder j hj] using hle
    · intro i hi j hj hj'
      rw [← horder j hj, ← horder i (hsub hi)]
      exact h.order_le _ (Finset.mem_map_of_mem _ hi) _ (Finset.mem_map_of_mem _ hj)
        (fun hm ↦ hj' ((Finset.mem_map' _).mp hm))
  · intro h
    refine ⟨Finset.map_subset_map.mpr h.subset, ?_, ?_, ?_⟩
    · simpa only [Finset.card_map] using h.card_eq
    · intro i hi j hj hji hle
      obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp hj
      refine Finset.mem_map_of_mem _ (h.mem_of_lt_of_le i₀ hi₀ j₀ hj₀ (e.lt_iff_lt.mp hji) ?_)
      simpa only [RelEmbedding.coe_toEmbedding, horder i₀ (h.subset hi₀), horder j₀ hj₀] using hle
    · intro i hi j hj hj'
      obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_map.mp hj
      simpa only [RelEmbedding.coe_toEmbedding, horder i₀ (h.subset hi₀), horder j₀ hj₀] using
        h.order_le i₀ hi₀ j₀ hj₀ (fun hjmem ↦ hj' (Finset.mem_map_of_mem _ hjmem))

/-- Transport a selection between two copies of the retained stages, with the same orders and
relative stage order. The transported selection has the same sum of orders. -/
theorem exists_reindex (h : IsPositiveSectionSelection s order steps selected)
    (source : κ ↪o ι) (target : κ ↪o ι') (retained : Finset κ)
    (hs : s = retained.map source.toEmbedding) (order' : ι' → ℤ)
    (horder : ∀ i ∈ retained, order' (target i) = order (source i)) :
    ∃ indices ⊆ retained, selected = indices.map source.toEmbedding ∧
      IsPositiveSectionSelection (retained.map target.toEmbedding) order' steps
        (indices.map target.toEmbedding) ∧
      (∑ i ∈ indices.map target.toEmbedding, order' i) = ∑ i ∈ selected, order i := by
  subst s
  obtain ⟨indices, hsub, rfl⟩ := Finset.subset_map_iff.mp h.subset
  refine ⟨indices, hsub, rfl, ?_, ?_⟩
  · exact (map_iff target retained indices (order ∘ source) horder).mpr
      ((map_iff source retained indices (order ∘ source) (fun _ _ ↦ rfl)).mp h)
  · simp only [Finset.sum_map, RelEmbedding.coe_toEmbedding]
    exact Finset.sum_congr rfl (fun i hi ↦ horder i (hsub hi))

/-- Transport the selection through a pivot at the earliest maximal stage `p` when the
reverse center is off the positive section and the remaining stages retain their orders.
If the new fiber coefficient is `a - order p`, subtracting the remaining selected orders
gives the same final coefficient as subtracting all originally selected orders from `a`. -/
theorem of_pivot {n k : ℕ} {s selected : Finset (Fin (n + 1))}
    {order : Fin (n + 1) → ℤ} {s' : Finset (Fin (1 + n))}
    {order' : Fin (1 + n) → ℤ} (h : IsPositiveSectionSelection s order (k + 1) selected)
    {p : Fin (n + 1)} (hp : p ∈ s)
    (hmax : ∀ i ∈ s, order i ≤ order p)
    (hearly : ∀ i ∈ s, i < p → order i < order p)
    (hhead : Fin.castAdd n (0 : Fin 1) ∉ s')
    (hstages : ∀ i : Fin n, i.natAdd 1 ∈ s' ↔ p.succAbove i ∈ s)
    (horder : ∀ i : Fin n, p.succAbove i ∈ s → order' (i.natAdd 1) = order (p.succAbove i)) :
    ∃ selected', IsPositiveSectionSelection s' order' k selected' ∧
      (∀ i : Fin n, i.natAdd 1 ∈ selected' ↔ p.succAbove i ∈ selected) ∧
      ∀ a : ℤ, a - order p - (∑ i ∈ selected', order' i) = a - ∑ i ∈ selected, order i := by
  let retained := Finset.univ.filter (fun i : Fin n ↦ p.succAbove i ∈ s)
  have hs : s.erase p = retained.map (Fin.succAboveOrderEmb p).toEmbedding := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_map, Fin.succAboveOrderEmb_toEmbedding,
      Fin.succAboveEmb_apply, retained, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hi⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hne
      exact ⟨j, hi, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Fin.succAbove_ne p j, hj⟩
  have hs' : s' = retained.map (Fin.natAddOrderEmb 1).toEmbedding := by
    ext i
    simp only [Fin.natAddOrderEmb_toEmbedding]
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · obtain rfl := Subsingleton.elim j (0 : Fin 1)
      simp only [hhead, Finset.mem_map, Fin.natAddEmb_apply, false_iff]
      rintro ⟨l, -, he⟩
      have hval := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero] at hval
      omega
    · rw [← Fin.natAddEmb_apply, Finset.mem_map']
      simpa only [retained, Finset.mem_filter, Finset.mem_univ, true_and, Fin.natAddEmb_apply] using
        hstages j
  have hmem := h.mem_of_earliest_max hp hmax hearly
  obtain ⟨indices, -, hindices, hselected', hsum⟩ := (h.erase hmem).exists_reindex
    (Fin.succAboveOrderEmb p) (Fin.natAddOrderEmb 1) retained hs order'
    (fun i hi ↦ horder i (Finset.mem_filter.mp hi).2)
  refine ⟨indices.map (Fin.natAddOrderEmb 1).toEmbedding, hs'.symm ▸ hselected', ?_, fun a ↦ ?_⟩
  · intro i
    simp only [Fin.natAddOrderEmb_toEmbedding, ← Fin.natAddEmb_apply, Finset.mem_map']
    have hi : p.succAbove i ∈ selected.erase p ↔ i ∈ indices := by
      rw [hindices, Fin.succAboveOrderEmb_toEmbedding, ← Fin.succAboveEmb_apply, Finset.mem_map']
    rw [Finset.mem_erase, and_iff_right (Fin.succAbove_ne p i)] at hi
    exact hi.symm
  · have hpivot := Finset.add_sum_erase selected order hmem
    omega

end IsPositiveSectionSelection

end QPainleve
