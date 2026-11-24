/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Adjacency

import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Corners of a Hirzebruch fan

Every two-ray cone is spanned by a section ray and a fiber ray. Its primitive generators,
in that order, give a Hirzebruch basis for the same ruling at the selected corner.
This supplies the coordinates for the toric elementary link in Lutz's
[proof of Proposition 8.11](https://arxiv.org/pdf/2005.05010v3#page=71).
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)

open Classical in
/-- The four primitive generators in Hirzebruch normal form give an indexing
of the rays by `Fin 4`. -/
theorem exists_rayEquiv_of_hirzebruch_ray_generators
    (h : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, e • b 0 - b 1}) :
    ∃ r : Fin 4 ≃ Φ.Ray,
      (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1] := by
  let v : Fin 4 → N := ![b 0, b 1, -b 0, e • b 0 - b 1]
  have hv : Set.range v = Set.range (Ray.primitiveGenerator (Phi := Φ)) := by
    rw [h]
    ext x
    simp [v, or_comm, or_left_comm, or_assoc]
  have hinj : Function.Injective v := by
    intro j k hjk
    have h₀ := congrArg (b.coord 0) hjk
    have h₁ := congrArg (b.coord 1) hjk
    fin_cases j <;> fin_cases k <;> norm_num [v, Basis.coord_apply] at *
  let rays := Equiv.ofInjective _ (Ray.primitiveGenerator_injective (Φ := Φ))
  let vectors := (Equiv.ofInjective v hinj).trans (Set.equivOfEq hv)
  refine ⟨vectors.trans rays.symm, funext fun j ↦ ?_⟩
  exact congrArg Subtype.val (rays.apply_symm_apply (vectors j))

variable (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

include hr in
/-- Swapping the two fiber rays of a Hirzebruch marking admits a lattice basis
with the same signed Hirzebruch parameter. -/
theorem exists_hirzebruch_marking_swap_fibers :
    ∃ (d : Basis (Fin 2) ℤ N),
      (fun j ↦ (r (Equiv.swap 1 3 j)).primitiveGenerator) =
        ![d 0, d 1, -d 0, e • d 0 - d 1] := by
  let d := (b.map (LinearEquiv.transvection (f := (-e) • b.coord 1) (v := b 0)
    (by simp [Basis.coord_apply]))).unitsSMul (fun j ↦ if j = 1 then (-1 : ℤˣ) else 1)
  have h₀ : d 0 = b 0 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply]
  have h₁ : d 1 = e • b 0 - b 1 := by
    simp [d, Basis.unitsSMul_apply, LinearMap.transvection.apply, Basis.coord_apply,
      sub_eq_add_neg, add_comm]
  refine ⟨d, funext fun j ↦ ?_⟩
  fin_cases j <;> simp [Equiv.swap_apply_def, h₀, h₁, congrFun hr]

local notation "sec" j:arg => r ((![0, 2] : Fin 2 → Fin 4) j)
local notation "fib" j:arg => r ((![1, 3] : Fin 2 → Fin 4) j)

include hr in
/-- The two fiber rays are exactly the neighbors of each section ray. -/
theorem hirzebruch_section_neighbors_iff (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (j : Fin 2) (τ : Φ.Ray) :
    (sec j ≠ τ ∧ ∃ σ : Φ.cones, (sec j).toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
      τ = r 1 ∨ τ = r 3 := by
  obtain ⟨prev, next, hp, hn, h⟩ := Φ.exists_ray_neighbors b hΦ hc (sec j)
  have hsec : (sec j).primitiveGenerator = b 0 ∨ (sec j).primitiveGenerator = -b 0 := by
    fin_cases j
    · exact Or.inl (congrFun hr 0)
    · exact Or.inr (congrFun hr 2)
  have hmem (τ : Φ.Ray) (hd : b.detDualEquiv (sec j).primitiveGenerator τ.primitiveGenerator ≠ 0) :
      τ ∈ ({r 1, r 3} : Set Φ.Ray) := by
    obtain ⟨k, rfl⟩ := r.surjective τ
    fin_cases k <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    · exact (hd (by rcases hsec with hs | hs <;>
        simp [hs, congrFun hr 0, -Basis.detDualEquiv_apply, b.detDualEquiv_self])).elim
    · exact Or.inl rfl
    · exact (hd (by rcases hsec with hs | hs <;>
        simp [hs, congrFun hr 2, -Basis.detDualEquiv_apply, b.detDualEquiv_self])).elim
    · exact Or.inr rfl
  have hne : prev ≠ next := fun he ↦ by rw [he, hn] at hp; omega
  classical
  have hset : ({prev, next} : Set Φ.Ray) = {r 1, r 3} := by
    apply Set.eq_of_subset_of_ncard_le
    · exact Set.pair_subset (hmem prev (by rw [hp]; decide)) (hmem next (by rw [hn]; decide))
    · rw [Set.ncard_pair (r.injective.ne (by decide)), Set.ncard_pair hne]
    · exact Set.finite_insert.mpr (Set.finite_singleton _)
  rw [h τ]
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using Set.ext_iff.mp hset τ

include hr in
/-- Each section ray of a complete regular Hirzebruch fan shares a cone with each fiber ray. -/
theorem exists_cone_of_hirzebruch_section_fiber (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (j k : Fin 2) :
    ∃ σ : Φ.cones, (sec j).toCone ≤ σ ∧ (fib k).toCone ≤ σ := by
  have hk : fib k = r 1 ∨ fib k = r 3 := by
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact ((hirzebruch_section_neighbors_iff b e r hr hΦ hc j (fib k)).mpr hk).2

include hr in
/-- The supremum of a section ray and a fiber ray is a cone of a complete regular
Hirzebruch fan. -/
theorem hirzebruch_corner_mem (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (j k : Fin 2) :
    (sec j).toCone.val ⊔ (fib k).toCone.val ∈ Φ.cones := by
  obtain ⟨σ, hs, hf⟩ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc j k
  have hne : sec j ≠ fib k := by
    apply r.injective.ne
    fin_cases j <;> fin_cases k <;> decide
  have hd : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  rw [← Φ.cone_eq_sup_of_ray_ne_of_le hΦ hd hne hs hf]
  exact σ.property

include hr in
private theorem hirzebruch_fiber_neighbors (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (τ : Φ.Ray) :
    (r 1 ≠ τ ∧ ∃ σ : Φ.cones, (r 1).toCone ≤ σ ∧ τ.toCone ≤ σ) ↔ τ = r 0 ∨ τ = r 2 := by
  have h₀ : b.detDualEquiv (r 0).primitiveGenerator (r 1).primitiveGenerator = 1 := by
    rw [congrFun hr 0, congrFun hr 1]
    exact b.detDualEquiv_apply_basis_zero_one
  have h₂ : b.detDualEquiv (r 1).primitiveGenerator (r 2).primitiveGenerator = 1 := by
    rw [congrFun hr 1, congrFun hr 2]
    simp [-Basis.detDualEquiv_apply, b.detDualEquiv_swap (b 1) (b 0),
      b.detDualEquiv_apply_basis_zero_one]
  exact Φ.ray_neighbors_iff_of_det b hΦ hc
    ⟨h₀, exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 0⟩
    ⟨h₂, (exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 1 0).imp
      (fun _ h ↦ h.symm)⟩ τ

include hr in
private theorem exists_hirzebruch_section_fiber_le (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) :
    ∃ j k : Fin 2, (sec j).toCone ≤ σ ∧ (fib k).toCone ≤ σ := by
  obtain ⟨p, q, hp, hq, hd⟩ :=
    Φ.exists_ray_pair_le_det_eq_one b ((isRegular_iff.mp hΦ) _ σ.property) hσ
  have hpq : p ≠ q := by
    rintro rfl
    rw [b.detDualEquiv_self] at hd
    omega
  have hcases (a : Φ.Ray) : (∃ j : Fin 2, a = sec j) ∨ (∃ k : Fin 2, a = fib k) := by
    obtain ⟨j, rfl⟩ := r.surjective a
    fin_cases j
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  have fromSection {j : Fin 2} {a : Φ.Ray}
      (hne : sec j ≠ a) (hs : (sec j).toCone ≤ σ) (ha : a.toCone ≤ σ) :
      ∃ j k : Fin 2, (sec j).toCone ≤ σ ∧ (fib k).toCone ≤ σ := by
    rcases (hirzebruch_section_neighbors_iff b e r hr hΦ hc j a).mp
        ⟨hne, σ, hs, ha⟩ with h | h
    · exact ⟨j, 0, hs, h ▸ ha⟩
    · exact ⟨j, 1, hs, h ▸ ha⟩
  rcases hcases p with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · exact fromSection hpq hp hq
  rcases hcases q with ⟨j, rfl⟩ | ⟨l, rfl⟩
  · exact ⟨j, k, hq, hp⟩
  have noBoth (h₁ : (r 1).toCone ≤ σ) (h₃ : (r 3).toCone ≤ σ) : False := by
    have h := (hirzebruch_fiber_neighbors b e r hr hΦ hc (r 3)).mp
      ⟨r.injective.ne (by decide), σ, h₁, h₃⟩
    simp only [Equiv.apply_eq_iff_eq, Fin.reduceEq, or_self] at h
  fin_cases k <;> fin_cases l
  · exact (hpq rfl).elim
  · exact (noBoth hp hq).elim
  · exact (noBoth hq hp).elim
  · exact (hpq rfl).elim

include hr in
private theorem hirzebruch_corner_ray_order {d : Basis (Fin 2) ℤ N} (j k : Fin 2)
    (h₀ : d 0 = (sec j).primitiveGenerator) (h₁ : d 1 = (fib k).primitiveGenerator) :
    ∃ (a : ℤ) (t : Fin 4 ≃ Φ.Ray),
      (fun l ↦ (t l).primitiveGenerator) = ![d 0, d 1, -d 0, a • d 0 - d 1] ∧
      (t 1 = r 1 ∨ t 1 = r 3) ∧
      ((t 0 = r 0 ∧ a = e) ∨ (t 0 = r 2 ∧ a = -e)) := by
  let p : Equiv.Perm (Fin 4) := if j = 0 then Equiv.refl _ else Equiv.swap 0 2
  let q : Equiv.Perm (Fin 4) := if k = 0 then Equiv.refl _ else Equiv.swap 1 3
  refine ⟨if j = 0 then e else -e, (p.trans q).trans r, ?_, ?_, ?_⟩
  · funext l
    fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [p, q, h₀, h₁, congrFun hr, Equiv.swap_apply_def, smul_neg, neg_smul]
  · fin_cases k <;> fin_cases j <;> simp [p, q, Equiv.swap_apply_def]
  · fin_cases j <;> fin_cases k <;> simp [p, q, Equiv.swap_apply_def]

include hr in
/-- Keeping the first fiber ray and choosing the opposite section negates the
Hirzebruch parameter in the ray presentation of the same fan. -/
theorem exists_hirzebruch_opposite_section_basis :
    ∃ (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Φ.Ray),
      (fun l ↦ (t l).primitiveGenerator) = ![d 0, d 1, -d 0, (-e) • d 0 - d 1] ∧
      t 1 = r 1 ∧ t 0 = r 2 := by
  let d := b.unitsSMul ![-1, 1]
  have h₀ : d 0 = (r 2).primitiveGenerator := by
    simp [d, Basis.unitsSMul_apply, congrFun hr 2]
  have h₁ : d 1 = (r 1).primitiveGenerator := by
    simp [d, Basis.unitsSMul_apply, congrFun hr 1]
  obtain ⟨a, t, ht, -, ha⟩ := hirzebruch_corner_ray_order b e r hr (d := d) 1 0 h₀ h₁
  have ht₂ : t 0 = r 2 :=
    Ray.primitiveGenerator_injective ((congrFun ht 0).trans h₀)
  have ht₁ : t 1 = r 1 :=
    Ray.primitiveGenerator_injective ((congrFun ht 1).trans h₁)
  rcases ha with ⟨he, -⟩ | ⟨-, rfl⟩
  · exact (r.injective.ne (by decide : (0 : Fin 4) ≠ 2) (he.symm.trans ht₂)).elim
  · exact ⟨d, t, ht, ht₁, ht₂⟩

include hr in
/-- At any corner of a complete regular Hirzebruch fan, the section and fiber
generators give another Hirzebruch basis for the same ruling. Ray one in the
new numbering is one of the original two fiber rays. Choosing the other section negates the
signed Hirzebruch parameter. -/
theorem exists_hirzebruch_corner_basis (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (σ : Φ.cones) (hσ : Nat.card (ToricRay σ.val) = 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (a : ℤ) (t : Fin 4 ≃ Φ.Ray),
      σ.val = hull ℝ (Set.range (i ∘ d)) ∧
      (fun l ↦ (t l).primitiveGenerator) = ![d 0, d 1, -d 0, a • d 0 - d 1] ∧
      (t 1 = r 1 ∨ t 1 = r 3) ∧
      ((t 0 = r 0 ∧ a = e) ∨ (t 0 = r 2 ∧ a = -e)) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨j, k, hs, hf⟩ := exists_hirzebruch_section_fiber_le b e r hr hΦ hc σ hσ
  have hne : sec j ≠ fib k := by
    apply r.injective.ne
    fin_cases j <;> fin_cases k <;> decide
  obtain ⟨d, h₀, h₁⟩ :=
    Φ.exists_basis_of_ray_ne_of_le ((isRegular_iff.mp hΦ) _ σ.property) hN hne hs hf
  obtain ⟨a, t, ht, htf, hts⟩ := hirzebruch_corner_ray_order b e r hr j k h₀ h₁
  refine ⟨d, a, t, ?_, ht, htf, hts⟩
  rw [Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN hne hs hf, (sec j).toCone_eq_hull_primitiveGenerator,
    (fib k).toCone_eq_hull_primitiveGenerator, ← h₀, ← h₁, ← Submodule.span_union]
  congr 1
  ext x
  simp [Fin.exists_fin_succ, eq_comm, or_comm]

end TauCeti.Toric.Fan
