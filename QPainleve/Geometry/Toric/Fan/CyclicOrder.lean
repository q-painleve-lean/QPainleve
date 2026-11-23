/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import QPainleve.Geometry.Toric.Fan.Adjacency

import Mathlib.Analysis.Normed.Module.Connected
import QPainleve.GroupTheory.Perm.Cycle

/-!
# Cyclic orders of complete regular fans

The rays of a complete regular rank-two fan admit a cyclic numbering from any
starting ray. The positive determinant determines the successor and the cyclic
order. The numbering gives the order of the toric boundary divisors used in the
boundary self-intersection recurrence.
-/

public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

private theorem exists_ray_succPerm (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    ∃ p : Equiv.Perm Φ.Ray, ∀ ρ τ : Φ.Ray, p ρ = τ ↔
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ := by
  classical
  choose next hnext huniq using fun ρ ↦ (exists_unique_ray_neighbor_on_each_side b hΦ hc ρ).1
  have hnext_iff (ρ τ : Φ.Ray) : next ρ = τ ↔
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ :=
    ⟨fun h ↦ h ▸ hnext ρ, fun h ↦ (huniq ρ τ h).symm⟩
  have hinj : Function.Injective next := by
    intro ρ τ h
    obtain ⟨prev, _, hprev⟩ := (exists_unique_ray_neighbor_on_each_side b hΦ hc (next τ)).2
    have hback (υ : Φ.Ray) (hυ : next υ = next τ) : υ = prev := by
      obtain ⟨hd, σ, hυσ, hnextσ⟩ := (hnext_iff υ (next τ)).mp hυ
      exact hprev υ ⟨by rw [b.detDualEquiv_swap, hd], σ, hnextσ, hυσ⟩
    exact (hback ρ h).trans (hback τ rfl).symm
  exact ⟨Equiv.ofBijective next (Finite.injective_iff_bijective.mp hinj), hnext_iff⟩

private theorem sameCycle_of_ray_le (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (p : Equiv.Perm Φ.Ray)
    (hp : ∀ ρ τ : Φ.Ray, p ρ = τ ↔
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    p.SameCycle ρ τ := by
  by_cases he : ρ = τ
  · rw [he]
  have hu := isUnit_det_of_ray_ne_of_le b ((isRegular_iff.1 hΦ) _ σ.property) he hρ hτ
  rcases Int.isUnit_iff.mp hu with hd | hd
  · exact ⟨1, by simpa only [zpow_one] using (hp ρ τ).mpr ⟨hd, σ, hρ, hτ⟩⟩
  · apply Equiv.Perm.SameCycle.symm
    refine ⟨1, ?_⟩
    rw [zpow_one, hp, b.detDualEquiv_swap, hd, neg_neg]
    exact ⟨rfl, σ, hτ, hρ⟩

private theorem exists_ray_le_of_mem_ne_zero {σ : Φ.cones} {z : V}
    (hz : z ∈ σ.val) (hne : z ≠ 0) : ∃ ρ : Φ.Ray, ρ.toCone ≤ σ :=
  Φ.exists_ray_le_of_ne_bot σ fun h ↦ hne (by simpa [h] using hz)

-- Each cone away from the origin lies on one side of a partition of the ray set
-- whose membership is constant on rays sharing a cone.
private theorem eq_univ_of_ray_partition (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (S : Set Φ.Ray) (hS : S.Nonempty)
    (hpartition : ∀ (σ : Φ.cones) (ρ τ : Φ.Ray), ρ.toCone ≤ σ → τ.toCone ≤ σ →
      (ρ ∈ S ↔ τ ∈ S)) :
    S = Set.univ := by
  classical
  let e := (Φ.lattice.isBaseChange.basis b).equivFun
  let U (A : Set Φ.Ray) := ⋃ σ ∈ {σ : Φ.cones | ∀ ρ : Φ.Ray, ρ.toCone ≤ σ → ρ ∈ A},
    e.symm ⁻¹' (σ.val : Set V)
  have hclosed (A : Set Φ.Ray) : IsClosed (U A) := Set.toFinite _ |>.isClosed_biUnion
    fun σ _ ↦ isClosed_preimage_cone_of_isRegular hΦ σ e.symm
      fun l ↦ (l.comp e.symm.toLinearMap).continuous_of_finiteDimensional
  have hmem (A : Set Φ.Ray) {ρ : Φ.Ray} (hρ : ∀ τ : Φ.Ray, τ.toCone ≤ ρ.toCone → τ ∈ A) :
      e (i ρ.primitiveGenerator) ∈ ({0}ᶜ : Set (Fin 2 → ℝ)) ∩ U A := by
    refine ⟨?_, Set.mem_iUnion₂.mpr ⟨ρ.toCone, hρ, ?_⟩⟩
    · exact fun h ↦ ρ.primitiveGenerator_ne_zero (Φ.lattice.injective (by
        simpa only [e.injective.eq_iff, ← map_zero e, ← map_zero i, Set.mem_singleton_iff] using h))
    · have hr : i ρ.primitiveGenerator ∈ (ρ.toCone.val : Set V) := ρ.primitiveGenerator_mem
      simpa only [Set.mem_preimage, e.symm_apply_apply] using hr
  have hcover : ({0}ᶜ : Set (Fin 2 → ℝ)) ⊆ U S ∪ U Sᶜ := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := Φ.isComplete_iff.mp hc (e.symm x)
    let c : Φ.cones := ⟨σ, hσ⟩
    have hx₀ : e.symm x ≠ 0 := fun h ↦ hx (by simpa using congrArg e h)
    obtain ⟨ρ, hρ⟩ := exists_ray_le_of_mem_ne_zero (σ := c) hxσ hx₀
    by_cases hm : ρ ∈ S
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨c, fun τ hτ ↦ (hpartition c ρ τ hρ hτ).mp hm, hxσ⟩)
    · refine Or.inr (Set.mem_iUnion₂.mpr ⟨c, ?_, hxσ⟩)
      exact fun τ hτ h ↦ hm ((hpartition c ρ τ hρ hτ).mpr h)
  apply Set.eq_univ_of_forall
  by_contra! h
  obtain ⟨ρ, hρ⟩ := hS
  obtain ⟨τ, hτ⟩ := h
  have hdim : 1 < Module.rank ℝ (Fin 2 → ℝ) := by
    simp [← Module.finrank_eq_rank, Module.finrank_fintype_fun_eq_card]
  have hnonempty := isPreconnected_closed_iff.mp
    (isConnected_compl_singleton_of_one_lt_rank hdim 0).isPreconnected _ _
    (hclosed S) (hclosed Sᶜ) hcover
    ⟨_, hmem S (fun υ hυ ↦ (hpartition ρ.toCone ρ υ le_rfl hυ).mp hρ)⟩
    ⟨_, hmem Sᶜ (fun υ hυ hh ↦ hτ ((hpartition τ.toCone τ υ le_rfl hυ).mpr hh))⟩
  obtain ⟨x, hx, hU, hU'⟩ := hnonempty
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp hU
  obtain ⟨σ', hσ', hxσ'⟩ := Set.mem_iUnion₂.mp hU'
  have hx₀ : e.symm x ≠ 0 := fun h ↦ hx (by simpa using congrArg e h)
  obtain ⟨υ, hυ⟩ := exists_ray_le_of_mem_ne_zero (σ := σ ⊓ σ') ⟨hxσ, hxσ'⟩ hx₀
  exact (hσ' υ (hυ.trans inf_le_right)) (hσ υ (hυ.trans inf_le_left))

private theorem isCycleOn_univ_of_ray_succPerm (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (p : Equiv.Perm Φ.Ray)
    (hp : ∀ ρ τ : Φ.Ray, p ρ = τ ↔
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) :
    p.IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.mpr p.bijective, fun ρ _ τ _ ↦ ?_⟩
  let S : Set Φ.Ray := {υ | p.SameCycle ρ υ}
  have hS : S = Set.univ := eq_univ_of_ray_partition b hΦ hc S ⟨ρ, .rfl⟩
    fun σ μ ν hμ hν ↦ by
      have h := sameCycle_of_ray_le b hΦ p hp hμ hν
      exact ⟨fun hm ↦ hm.trans h, fun hn ↦ hn.trans h.symm⟩
  have hτ : τ ∈ S := hS.symm ▸ Set.mem_univ τ
  exact hτ

/-- From any starting ray, a complete regular rank-two fan has a unique numbering by
the cyclic group of order the number of rays. Consecutive rays share a cone and
have determinant one in the orientation chosen by the basis. -/
theorem existsUnique_cyclicRayNumbering (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (ρ₀ : Φ.Ray) :
    ∃! u : ZMod (Nat.card Φ.Ray) ≃ Φ.Ray, u 0 = ρ₀ ∧
      ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ := by
  obtain ⟨p, hp⟩ := exists_ray_succPerm b hΦ hc
  obtain ⟨u, hu₀, hu⟩ := (isCycleOn_univ_of_ray_succPerm b hΦ hc p hp).exists_zmod_equiv ρ₀
  refine ⟨u, ⟨hu₀, fun j ↦ (hp _ _).mp (hu j).symm⟩, ?_⟩
  rintro v ⟨hv₀, hv⟩
  let : Nonempty Φ.Ray := ⟨ρ₀⟩
  let : NeZero (Nat.card Φ.Ray) := ⟨Nat.card_pos.ne'⟩
  apply Equiv.ext
  refine ZMod.natCast_zmod_surjective.forall.mpr fun a ↦ ?_
  induction a with
  | zero => simpa only [Nat.cast_zero] using hv₀.trans hu₀.symm
  | succ a ih => rw [Nat.cast_succ, hu, ← (hp _ _).mpr (hv _), ih]

/-- A two-ray cone of a regular rank-two fan contains an ordered pair of rays whose
primitive generators have determinant one in the chosen lattice basis. -/
theorem exists_ray_pair_le_det_eq_one (b : Module.Basis (Fin 2) ℤ N)
    {σ : Φ.cones} (hσ : IsRegularCone i σ.val) (hcard : Nat.card (ToricRay σ.val) = 2) :
    ∃ ρ τ : Φ.Ray, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ ∧
      b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 := by
  have : Finite (ToricRay σ.val) := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  let := Fintype.ofFinite (ToricRay σ.val)
  let e := (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card).symm.trans hcard)).symm.trans
    (Φ.rayEquiv σ).symm
  let ρ : Φ.Ray := (e 0).val
  let τ : Φ.Ray := (e 1).val
  have hρθ : ρ ≠ τ := fun h ↦ zero_ne_one (e.injective (Subtype.ext h))
  rcases Int.isUnit_iff.mp
    (isUnit_det_of_ray_ne_of_le b hσ hρθ (e 0).property (e 1).property) with hd | hd
  · exact ⟨ρ, τ, (e 0).property, (e 1).property, hd⟩
  · exact ⟨τ, ρ, (e 1).property, (e 0).property, by rw [b.detDualEquiv_swap, hd, neg_neg]⟩

/-- A positively oriented ray numbering of a complete regular rank-two fan numbers its
two-ray cones: cone `j` contains rays `j` and `j + 1`. -/
theorem exists_cyclicConeNumbering (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {n : ℕ} (u : ZMod n ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) :
    ∃ c : ZMod n ≃ {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2}, ∀ j,
      (u j).toCone ≤ (c j).val ∧ (u (j + 1)).toCone ≤ (c j).val := by
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  choose σ h₀ h₁ using fun j ↦ (hu j).2
  have hne (j : ZMod n) : u j ≠ u (j + 1) := by
    intro he
    have hdet := (hu j).1
    rw [← he, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  let c (j : ZMod n) : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2} :=
    ⟨σ j, Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim (hne j) (h₀ j) (h₁ j)⟩
  have hs (j : ZMod n) :
      ∀ ρ : Φ.Ray, ρ.toCone ≤ σ j → ρ = u j ∨ ρ = u (j + 1) := by
    intro ρ hρ
    let e := Φ.rayEquiv (σ j)
    have hr : e ⟨ρ, hρ⟩ ∈ ({e ⟨u j, h₀ j⟩, e ⟨u (j + 1), h₁ j⟩} : Set _) := by
      simp only [e, rayEquiv_apply]
      rw [Φ.toricRays_eq_pair ((isRegular_iff.mp hΦ) _ (σ j).property) hdim
        (hne j) (h₀ j) (h₁ j)]
      exact Set.mem_univ _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, e.injective.eq_iff,
      Subtype.mk.injEq] using hr
  refine ⟨Equiv.ofBijective c ⟨?_, ?_⟩, fun j ↦ ⟨h₀ j, h₁ j⟩⟩
  · intro j k h
    have he : σ j = σ k := congrArg Subtype.val h
    rcases hs k (u j) (he ▸ h₀ j) with hj | hj
    · exact u.injective hj
    rcases hs k (u (j + 1)) (he ▸ h₁ j) with hk | hk
    · have hdet := (hu j).1
      rw [hj, hk, b.detDualEquiv_swap, (hu k).1] at hdet
      omega
    exact (hne j (hj.trans hk.symm)).elim
  · intro t
    obtain ⟨r, s, hr, hs', hd⟩ := exists_ray_pair_le_det_eq_one b
      ((isRegular_iff.mp hΦ) _ t.val.property) t.property
    obtain ⟨j, rfl⟩ := u.surjective r
    obtain ⟨_, _, huniq⟩ := (exists_unique_ray_neighbor_on_each_side b hΦ hc (u j)).1
    have he : s = u (j + 1) := (huniq s ⟨hd, t.val, hr, hs'⟩).trans
      (huniq (u (j + 1)) (hu j)).symm
    subst s
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    exact (cone_eq_sup_of_ray_ne_of_le hΦ hdim (hne j) (h₀ j) (h₁ j)).trans
      (cone_eq_sup_of_ray_ne_of_le hΦ hdim (hne j) hr hs').symm

end TauCeti.Toric.Fan
