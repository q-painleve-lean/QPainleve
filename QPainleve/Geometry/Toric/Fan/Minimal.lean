/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.CyclicOrder

import QPainleve.Geometry.Toric.Fan.HalfPlane
import TauCeti.Data.ZMod.Induction

/-!
# Minimal complete regular fans in rank two

The two neighbors of a ray add to an integer multiple of its primitive generator.
If the multiple is one, the ray can be removed by an inverse star subdivision.
If no such ray exists, the primitive generators have the projective-plane or
Hirzebruch normal form. See [Cox, Little and Schenck, *Toric Varieties*, Theorem 10.4.3][CLS]
for the classification.

The proof uses a longest primitive generator to find a triangle or an opposite
pair of rays. In an opposite pair's open half-plane, the neighbor relation at
a maximum of the integral height rules out any subdivision of that half-plane.
In the triangle case, a height on the complementary sector rules out additional rays.

[CLS]: https://doi.org/10.1090/gsm/124
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

private theorem ray_toCone_le_of_eq_nonneg_smul_add (r : Φ.Ray) (σ : Φ.cones)
    {p q : Φ.Ray} (hp : p.toCone ≤ σ) (hq : q.toCone ≤ σ) {x y : ℤ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : r.primitiveGenerator = x • p.primitiveGenerator + y • q.primitiveGenerator) :
    r.toCone ≤ σ := by
  rw [r.toCone_le_iff, hr, map_add, map_zsmul, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ]
  exact σ.val.add_mem (σ.val.smul_mem (by exact_mod_cast hx) (hp p.primitiveGenerator_mem))
    (σ.val.smul_mem (by exact_mod_cast hy) (hq q.primitiveGenerator_mem))

section Cyclic

variable {n : ℕ} (u : ZMod n ≃ Φ.Ray)
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
    ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)

local notation "v[" j "]" => Ray.primitiveGenerator (u j)
local notation "a[" j "]" => b.detDualEquiv v[j - 1] v[j + 1]

include hu in
private theorem succ_ne (j : ZMod n) : u j ≠ u (j + 1) := by
  intro h
  have hd := (hu j).1
  rw [← h, b.detDualEquiv_self] at hd
  omega

include hΦ hu in
private theorem exists_basis_of_cyclic_succ (j : ZMod n) :
    ∃ c : Basis (Fin 2) ℤ N, c 0 = v[j] ∧ c 1 = v[j + 1] := by
  obtain ⟨σ, hp, hq⟩ := (hu j).2
  exact exists_basis_of_ray_ne_of_le ((isRegular_iff.mp hΦ) _ σ.property)
    (by simpa using Module.finrank_eq_card_basis b) (succ_ne u b hu j) hp hq

include hu in
private theorem det_prev (j : ZMod n) : b.detDualEquiv v[j] v[j - 1] = -1 := by
  rw [b.detDualEquiv_swap]
  rw [show b.detDualEquiv v[j - 1] v[j] = 1 by
    simpa only [sub_add_cancel] using (hu (j - 1)).1]

include hΦ hu in
private theorem add_primitiveGenerator_eq_det_smul (j : ZMod n) :
    v[j - 1] + v[j + 1] = a[j] • v[j] := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_of_cyclic_succ u b hΦ hu (j - 1)
  rw [sub_add_cancel] at hc₁
  let x := v[j - 1] + v[j + 1]
  have hx : x = c.repr x 0 • v[j - 1] + c.repr x 1 • v[j] := by
    simpa only [Fin.sum_univ_two, hc₀, hc₁] using (c.sum_repr x).symm
  have hp : b.detDualEquiv v[j - 1] v[j] = 1 := by
    simpa only [sub_add_cancel] using (hu (j - 1)).1
  have hq := (hu j).1
  have hpneg := det_prev u b hu j
  have h₀ : c.repr x 0 = 0 := by
    have hd := congrArg (b.detDualEquiv v[j]) hx
    simp only [x, map_add, map_zsmul, hpneg, hq, b.detDualEquiv_self, smul_zero,
      Int.zsmul_eq_mul, mul_neg, mul_one, add_zero, neg_add_cancel] at hd
    simpa only [x, map_add] using neg_eq_zero.mp hd.symm
  have h₁ : c.repr x 1 = a[j] := by
    have hd := congrArg (b.detDualEquiv v[j - 1]) hx
    simpa only [x, map_add, map_zsmul, b.detDualEquiv_self, hp, smul_zero,
      Int.zsmul_eq_mul, mul_one, zero_add] using hd.symm
  simpa only [h₀, h₁, zero_smul, zero_add] using hx

include hu in
private theorem prev_ne_next (j : ZMod n) : u (j - 1) ≠ u (j + 1) := by
  intro h
  have he := congrArg (fun r : Φ.Ray ↦ b.detDualEquiv v[j] r.primitiveGenerator) h
  rw [det_prev u b hu j, (hu j).1] at he
  omega

-- The parallelogram identity bounds the sum of the two neighbors of a longest ray.
include hΦ hu in
private theorem exists_det_between_neg_one_and_one [NeZero n] :
    ∃ j, -1 ≤ a[j] ∧ a[j] ≤ 1 := by
  let sq (x : N) : ℤ := b.repr x 0 ^ 2 + b.repr x 1 ^ 2
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod n))
    (fun j ↦ sq v[j]) Finset.univ_nonempty
  have hpos {x : N} (hx : x ≠ 0) : 0 < sq x := by
    have hn : b.repr x 0 ≠ 0 ∨ b.repr x 1 ≠ 0 := by
      by_contra! h
      exact hx (b.repr.injective (by ext k; fin_cases k <;> simp [h.1, h.2]))
    rcases hn with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)
  have hd : 0 < sq (v[j - 1] - v[j + 1]) := hpos (sub_ne_zero.mpr fun he ↦
    prev_ne_next u b hu j (Ray.primitiveGenerator_injective he))
  have hv : 0 < sq v[j] := hpos (u j).primitiveGenerator_ne_zero
  have hpar : sq (v[j - 1] + v[j + 1]) + sq (v[j - 1] - v[j + 1]) =
      2 * sq v[j - 1] + 2 * sq v[j + 1] := by
    simp only [sq, map_add, map_sub, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have hsmul (m : ℤ) (x : N) : sq (m • x) = m ^ 2 * sq x := by
    simp only [sq, map_zsmul, Finsupp.smul_apply, Int.zsmul_eq_mul]
    ring
  rw [add_primitiveGenerator_eq_det_smul u b hΦ hu j, hsmul] at hpar
  have hlt : a[j] ^ 2 * sq v[j] < 4 * sq v[j] := by
    linarith only [hpar, hd, hj (j - 1) (Finset.mem_univ _), hj (j + 1) (Finset.mem_univ _)]
  have hsq : a[j] ^ 2 < (2 : ℤ) ^ 2 := lt_of_mul_lt_mul_right hlt hv.le
  obtain ⟨hlo, hhi⟩ := abs_lt_of_sq_lt_sq' hsq (by decide)
  exact ⟨j, by omega, by omega⟩

-- If the height is nonconstant, some maximum sits just before a lower value.
private theorem exists_max_succ_lt [NeZero n] (f : Φ.Ray → ℤ)
    (hn : ∃ j k, f (u j) ≠ f (u k)) :
    ∃ j, (∀ k, f (u k) ≤ f (u j)) ∧ f (u (j + 1)) < f (u j) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod n))
    (f ∘ u) Finset.univ_nonempty
  simp only [Function.comp_apply] at hj
  by_contra! h
  have hstep (k : ZMod n) (hk : f (u k) = f (u j)) : f (u (k + 1)) = f (u j) :=
    (hj _ (Finset.mem_univ _)).antisymm (hk ▸ h k fun l ↦ hk ▸ hj l (Finset.mem_univ l))
  have hconst (k : ZMod n) : f (u k) = f (u j) := by
    have hshift (t : ZMod n) : f (u (t + j)) = f (u j) :=
      ZMod.induction_on t (by simp) fun t ht ↦ by simpa only [add_right_comm] using hstep _ ht
    simpa only [sub_add_cancel] using hshift (k - j)
  obtain ⟨x, y, hxy⟩ := hn
  exact hxy ((hconst x).trans (hconst y).symm)

include hΦ hu in
private theorem eq_zero_of_max_with_nonneg_neighbors (hmin : ∀ j, a[j] ≠ 1)
    (f : N →ₗ[ℤ] ℤ) (j : ZMod n)
    (hj : 0 < f v[j]) (hmax : ∀ k, f v[k] ≤ f v[j]) (hs : f v[j + 1] < f v[j])
    (hp : 0 ≤ f v[j - 1]) (hq : 0 ≤ f v[j + 1]) :
    f v[j - 1] = 0 ∧ f v[j + 1] = 0 := by
  have h := congrArg f (add_primitiveGenerator_eq_det_smul u b hΦ hu j)
  simp only [map_add, map_zsmul, Int.zsmul_eq_mul] at h
  have hlo : 0 ≤ a[j] * f v[j] := by linarith only [h, hp, hq]
  have hhi : a[j] * f v[j] < 2 * f v[j] := by linarith only [h, hs, hmax (j - 1)]
  have hz : a[j] = 0 := by
    have h₀ := nonneg_of_mul_nonneg_left hlo hj
    have h₂ := lt_of_mul_lt_mul_right hhi hj.le
    have := hmin j
    omega
  rw [hz, zero_mul] at h
  omega

include hu in
private theorem det_sign_of_opposite {l m : ZMod n} (hm : v[m] = -v[l]) (j : ZMod n) :
    let f := b.detDualEquiv v[l]
    (0 ≤ f v[j] ∧ 0 ≤ f v[j + 1]) ∨ (f v[j] ≤ 0 ∧ f v[j + 1] ≤ 0) := by
  intro f
  obtain ⟨σ, hp, hq⟩ := (hu j).2
  have hs := Φ.detCharacter_nonneg_or_nonpos b (u l).primitiveGenerator_ne_zero
    (u l).hull_primitiveGenerator_mem (hm ▸ (u m).hull_primitiveGenerator_mem) σ
  have hval (t : ZMod n) :
      Φ.lattice.realCharacter f.toAddMonoidHom (i v[t]) = (f v[t] : ℝ) := by
    rw [IsIntegralLattice.realCharacter_apply]
    rfl
  have hr (t : ZMod n) (ht : (u t).toCone ≤ σ) : i v[t] ∈ σ.val :=
    ht (u t).primitiveGenerator_mem
  rcases hs with h | h
  · exact Or.inl ⟨by exact_mod_cast hval j ▸ h _ (hr j hp),
      by exact_mod_cast hval (j + 1) ▸ h _ (hr _ hq)⟩
  · exact Or.inr ⟨by exact_mod_cast hval j ▸ h _ (hr j hp),
      by exact_mod_cast hval (j + 1) ▸ h _ (hr _ hq)⟩

include hΦ hu in
private theorem det_pos_iff_of_opposite [NeZero n] (hmin : ∀ j, a[j] ≠ 1)
    {l m : ZMod n} (hm : v[m] = -v[l]) (k : ZMod n) :
    0 < b.detDualEquiv v[l] v[k] ↔ k = l + 1 := by
  let f := b.detDualEquiv v[l]
  have hl : f v[l] = 0 := b.detDualEquiv_self _
  have hnext : f v[l + 1] = 1 := (hu l).1
  have hsign (t : ZMod n) :
      (0 ≤ f v[t] ∧ 0 ≤ f v[t + 1]) ∨ (f v[t] ≤ 0 ∧ f v[t + 1] ≤ 0) :=
    det_sign_of_opposite u b hu hm t
  have hstep : ∀ t, f v[t] ≤ 0 → 0 < f v[t + 1] → t = l := by
    intro t ht ht'
    obtain ⟨ht₀, _⟩ := (hsign t).resolve_right (fun h ↦ ht'.not_ge h.2)
    have hzero : b.detDualEquiv v[t] v[l] = 0 := by
      rw [b.detDualEquiv_swap, ht.antisymm ht₀, neg_zero]
    rcases (u l).eq_or_eq_neg_of_detCharacter_eq_zero b
      (u t).isPrimitiveGenerator.isPrimitive hzero with he | he
    · exact u.injective (Ray.primitiveGenerator_injective he)
    · have hdet := (hu t).1
      rw [he, map_neg, LinearMap.neg_apply] at hdet
      have hneg : -f v[t + 1] = 1 := hdet
      omega
  obtain ⟨j, hmax, hlt⟩ := exists_max_succ_lt u (fun r ↦ f r.primitiveGenerator)
    ⟨l, l + 1, by rw [hl, hnext]; exact zero_ne_one⟩
  have hj : 0 < f v[j] := (show 0 < f v[l + 1] by rw [hnext]; decide).trans_le (hmax _)
  have hp : 0 ≤ f v[j - 1] := by
    have hs := hsign (j - 1)
    rw [sub_add_cancel] at hs
    exact (hs.resolve_right (fun h ↦ hj.not_ge h.2)).1
  have hq := ((hsign j).resolve_right (fun h ↦ hj.not_ge h.1)).2
  obtain ⟨hp₀, hq₀⟩ :=
    eq_zero_of_max_with_nonneg_neighbors u b hΦ hu hmin f j hj hmax hlt hp hq
  have he : j = l + 1 := by
    have hh := hstep (j - 1) hp₀.le (by simpa only [sub_add_cancel] using hj)
    rw [← hh, sub_add_cancel]
  -- The positive successor of `l` is isolated, and no other step can enter
  -- the positive half-plane from a nonpositive height.
  have hprop (t : ZMod n) : 0 < f v[t] → t = l + 1 := by
    have hs (t : ZMod n) (ht : 0 < f v[t] → t = l + 1) (ht' : 0 < f v[t + 1]) :
        t + 1 = l + 1 := by
      by_cases h : 0 < f v[t]
      · rw [(ht h).trans he.symm, hq₀] at ht'
        exact (lt_irrefl _ ht').elim
      · rw [hstep t (le_of_not_gt h) ht']
    have hshift (k : ZMod n) : 0 < f v[k + l] → k + l = l + 1 :=
      ZMod.induction_on k (by simp [hl]) fun k hk ↦ by
        simpa only [add_right_comm] using hs (k + l) hk
    simpa only [sub_add_cancel] using hshift (t - l)
  exact ⟨hprop k, fun h ↦ h ▸ (by rw [hnext]; exact zero_lt_one)⟩

include hΦ hu in
private theorem range_of_opposite [NeZero n] (hmin : ∀ j, a[j] ≠ 1)
    {l m : ZMod n} (hm : v[m] = -v[l]) :
    Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {v[l], v[l + 1], v[m], v[l - 1]} := by
  have hneg (t : ZMod n) : b.detDualEquiv v[m] v[t] = -b.detDualEquiv v[l] v[t] := by
    rw [hm, map_neg, LinearMap.neg_apply]
  have hpos := det_pos_iff_of_opposite u b hΦ hu hmin hm
  have hneg' := det_pos_iff_of_opposite u b hΦ hu hmin (neg_eq_iff_eq_neg.mp hm.symm)
  have hprev : l - 1 = m + 1 := (hneg' _).mp (by rw [hneg, det_prev u b hu]; decide)
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨t, rfl⟩ := u.surjective r
    rcases lt_trichotomy (b.detDualEquiv v[l] v[t]) 0 with ht | ht | ht
    · exact Or.inr (Or.inr (Or.inr (congrArg (fun k ↦ v[k])
        (((hneg' t).mp (by rw [hneg]; omega)).trans hprev.symm))))
    · have hzero : b.detDualEquiv v[t] v[l] = 0 := by rw [b.detDualEquiv_swap, ht, neg_zero]
      rcases (u l).eq_or_eq_neg_of_detCharacter_eq_zero b
        (u t).isPrimitiveGenerator.isPrimitive hzero with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl (h.trans hm.symm)))
    · exact Or.inr (Or.inl (congrArg (fun k ↦ v[k]) ((hpos t).mp ht)))
  · rintro (rfl | rfl | rfl | rfl)
    all_goals exact ⟨_, rfl⟩

-- In the two adjacent cones the ray is one of the three listed rays. All other
-- rays lie strictly inside the complementary sector between the outer generators.
include hΦ hu in
private theorem repr_pos_of_outside_triangle {j t : ZMod n} (c : Basis (Fin 2) ℤ N)
    (hc₀ : c 0 = v[j - 1]) (hc₁ : c 1 = v[j])
    (htri : v[j + 1] = -v[j - 1] - v[j])
    (ht₀ : t ≠ j - 1) (ht₁ : t ≠ j) (ht₂ : t ≠ j + 1) :
    let x := c.repr v[t] 0
    let y := c.repr v[t] 1
    y < 0 ∧ y < x := by
  intro x y
  have ht : v[t] = x • v[j - 1] + y • v[j] := by
    simpa only [Fin.sum_univ_two, hc₀, hc₁] using (c.sum_repr v[t]).symm
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hp : ¬ (0 ≤ x ∧ 0 ≤ y) := by
    rintro ⟨hx, hy⟩
    obtain ⟨σ, hp, hr⟩ := (hu (j - 1)).2
    rw [sub_add_cancel] at hr
    have hne := succ_ne u b hu (j - 1)
    rw [sub_add_cancel] at hne
    rcases ray_eq_or_eq_of_le ((isRegular_iff.mp hΦ) _ σ.property) hN hne hp hr
      (ray_toCone_le_of_eq_nonneg_smul_add (u t) σ hp hr hx hy ht) with he | he
    · exact ht₀ (u.injective he)
    · exact ht₁ (u.injective he)
  have hq : ¬ (x ≤ 0 ∧ x ≤ y) := by
    rintro ⟨hx, hy⟩
    have ht' : v[t] = (y - x) • v[j] + (-x) • v[j + 1] := by
      rw [ht, htri, sub_smul, smul_sub, smul_neg, neg_smul, neg_smul, neg_neg]
      abel
    obtain ⟨σ, hr, hq⟩ := (hu j).2
    rcases ray_eq_or_eq_of_le ((isRegular_iff.mp hΦ) _ σ.property) hN (succ_ne u b hu j) hr hq
      (ray_toCone_le_of_eq_nonneg_smul_add (u t) σ hr hq (sub_nonneg.mpr hy)
        (neg_nonneg.mpr hx) ht') with he | he
    · exact ht₁ (u.injective he)
    · exact ht₂ (u.injective he)
  omega

include hΦ hu in
private theorem range_of_triangle [NeZero n] (hmin : ∀ j, a[j] ≠ 1)
    (j : ZMod n) (htri : v[j + 1] = -v[j - 1] - v[j]) :
    ∃ c : Basis (Fin 2) ℤ N,
      Set.range (Ray.primitiveGenerator (Phi := Φ)) = {c 0, c 1, -c 0 - c 1} := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_of_cyclic_succ u b hΦ hu (j - 1)
  rw [sub_add_cancel] at hc₁
  have hcover : ∀ t, t = j - 1 ∨ t = j ∨ t = j + 1 := by
    by_contra! ⟨t, ht₀, ht₁, ht₂⟩
    let f : N →ₗ[ℤ] ℤ := c.coord 0 - (2 : ℤ) • c.coord 1
    have heval (x : N) : f x = c.repr x 0 - 2 * c.repr x 1 := by
      simp [f, Basis.coord_apply]
    have hp : f v[j - 1] = 1 := by rw [← hc₀]; simp [heval]
    have hr : f v[j] = -2 := by rw [← hc₁]; simp [heval]
    have hq : f v[j + 1] = 1 := by rw [htri, ← hc₀, ← hc₁]; simp [heval]
    have hhigh (k : ZMod n) (h₀ : k ≠ j - 1) (h₁ : k ≠ j) (h₂ : k ≠ j + 1) :
        2 ≤ f v[k] := by
      have := repr_pos_of_outside_triangle u b hΦ hu c hc₀ hc₁ htri h₀ h₁ h₂
      rw [heval]
      omega
    obtain ⟨k, hk, hlt⟩ := exists_max_succ_lt u (fun r ↦ f r.primitiveGenerator)
      ⟨j - 1, j, by rw [hp, hr]; decide⟩
    have hk₂ : 2 ≤ f v[k] := (hhigh t ht₀ ht₁ ht₂).trans (hk t)
    have hne₀ : k ≠ j - 1 := fun h ↦ by rw [h, hp] at hk₂; omega
    have hne₁ : k ≠ j := fun h ↦ by rw [h, hr] at hk₂; omega
    have hne₂ : k ≠ j + 1 := fun h ↦ by rw [h, hq] at hk₂; omega
    have hpos (h : ZMod n) (hh : h ≠ j) : 0 < f v[h] := by
      by_cases h₀ : h = j - 1
      · rw [h₀, hp]; decide
      by_cases h₂ : h = j + 1
      · rw [h₂, hq]; decide
      exact (by decide : (0 : ℤ) < 2).trans_le (hhigh h h₀ hh h₂)
    have hback := hpos (k - 1) (fun h ↦ hne₂ (sub_eq_iff_eq_add.mp h))
    have hforw := hpos (k + 1) (fun h ↦ hne₀ (eq_sub_iff_add_eq.mpr h))
    exact hback.ne' (eq_zero_of_max_with_nonneg_neighbors u b hΦ hu hmin f k
      (by omega) hk hlt hback.le hforw.le).1
  refine ⟨c, ?_⟩
  rw [hc₀, hc₁, ← htri]
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨t, rfl⟩ := u.surjective r
    rcases hcover t with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

include hΦ hu in
private theorem range_hirzebruch_of_nonneg [NeZero n] (hmin : ∀ j, a[j] ≠ 1)
    {l m : ZMod n} (hm : v[m] = -v[l]) (ha : 0 ≤ a[l]) :
    ∃ c : Basis (Fin 2) ℤ N, ∃ e : ℕ, e ≠ 1 ∧
      Set.range (Ray.primitiveGenerator (Phi := Φ)) =
        {c 0, c 1, -c 0, (e : ℤ) • c 0 - c 1} := by
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_of_cyclic_succ u b hΦ hu l
  have hlast : v[l - 1] = a[l] • v[l] - v[l + 1] :=
    eq_sub_of_add_eq (add_primitiveGenerator_eq_det_smul u b hΦ hu l)
  refine ⟨c, (a[l]).toNat, ?_, ?_⟩
  · intro h
    have hf : ((a[l]).toNat : ℤ) = (1 : ℤ) := congrArg Int.ofNat h
    exact hmin l ((Int.toNat_of_nonneg ha).symm.trans hf)
  rw [Int.toNat_of_nonneg ha, hc₀, hc₁, range_of_opposite u b hΦ hu hmin hm, hm]
  exact congrArg (fun x ↦ ({v[l], v[l + 1], -v[l], x} : Set N)) hlast

include hΦ hu in
private theorem range_hirzebruch_of_opposite [NeZero n] (hmin : ∀ j, a[j] ≠ 1)
    {l m : ZMod n} (hm : v[m] = -v[l]) :
    ∃ c : Basis (Fin 2) ℤ N, ∃ e : ℕ, e ≠ 1 ∧
      Set.range (Ray.primitiveGenerator (Phi := Φ)) =
        {c 0, c 1, -c 0, (e : ℤ) • c 0 - c 1} := by
  by_cases ha : 0 ≤ a[l]
  · exact range_hirzebruch_of_nonneg u b hΦ hu hmin hm ha
  have hl : v[l] = -v[m] := neg_eq_iff_eq_neg.mp hm.symm
  have he₀ : m - 1 = l + 1 := (det_pos_iff_of_opposite u b hΦ hu hmin hm _).mp (by
    have h := det_prev u b hu m
    rw [hm, map_neg, LinearMap.neg_apply] at h
    omega)
  have he₁ : l - 1 = m + 1 := (det_pos_iff_of_opposite u b hΦ hu hmin hl _).mp (by
    rw [hm, map_neg, LinearMap.neg_apply, det_prev u b hu]
    decide)
  have he : a[m] = -a[l] := by
    rw [he₀, ← he₁, b.detDualEquiv_swap]
  exact range_hirzebruch_of_nonneg u b hΦ hu hmin hl (by omega)

end Cyclic

/-- A regular complete rank-two fan either has a ray whose two adjacent primitive
generators sum to its generator, or has the primitive generators of the projective
plane or a Hirzebruch surface of index different from one. -/
theorem exists_ray_eq_sum_or_exists_basis_ray_generators
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    (∃ p r q : Φ.Ray,
      (b.detDualEquiv p.primitiveGenerator r.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, p.toCone ≤ σ ∧ r.toCone ≤ σ) ∧
      (b.detDualEquiv r.primitiveGenerator q.primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, r.toCone ≤ σ ∧ q.toCone ≤ σ) ∧
      p.primitiveGenerator + q.primitiveGenerator = r.primitiveGenerator) ∨
    ∃ c : Basis (Fin 2) ℤ N,
      Set.range (Ray.primitiveGenerator (Phi := Φ)) = {c 0, c 1, -c 0 - c 1} ∨
      ∃ e : ℕ, e ≠ 1 ∧ Set.range (Ray.primitiveGenerator (Phi := Φ)) =
        {c 0, c 1, -c 0, (e : ℤ) • c 0 - c 1} := by
  let : Nontrivial N := ⟨b 0, 0, b.ne_zero 0⟩
  let : Nonempty Φ.Ray := Φ.nonempty_ray_of_isComplete hc
  let : NeZero (Nat.card Φ.Ray) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨u, ⟨-, hu⟩, -⟩ := existsUnique_cyclicRayNumbering b hΦ hc
    (Classical.choice ‹Nonempty Φ.Ray›)
  let v (j : ZMod (Nat.card Φ.Ray)) := (u j).primitiveGenerator
  by_cases h : ∃ j, b.detDualEquiv (v (j - 1)) (v (j + 1)) = 1
  · obtain ⟨j, hj⟩ := h
    refine Or.inl ⟨u (j - 1), u j, u (j + 1), ?_, hu j, ?_⟩
    · simpa only [sub_add_cancel] using hu (j - 1)
    · have hv : v (j - 1) + v (j + 1) =
          b.detDualEquiv (v (j - 1)) (v (j + 1)) • v j :=
        add_primitiveGenerator_eq_det_smul u b hΦ hu j
      rwa [hj, one_zsmul] at hv
  push Not at h
  obtain ⟨j, hj₀, hj₁⟩ := exists_det_between_neg_one_and_one u b hΦ hu
  have hj : b.detDualEquiv (v (j - 1)) (v (j + 1)) = -1 ∨
      b.detDualEquiv (v (j - 1)) (v (j + 1)) = 0 := by
    have hne := h j
    dsimp only [v] at hne ⊢
    omega
  have hv : v (j - 1) + v (j + 1) =
      b.detDualEquiv (v (j - 1)) (v (j + 1)) • v j :=
    add_primitiveGenerator_eq_det_smul u b hΦ hu j
  rcases hj with hj | hj
  · have hv' : v (j + 1) = -v (j - 1) - v j := by
      have hs : v (j - 1) + v (j + 1) = -v j := by
        simpa only [hj, neg_one_zsmul] using hv
      calc
        _ = -v j - v (j - 1) := eq_sub_of_add_eq ((add_comm _ _).trans hs)
        _ = _ := by abel
    obtain ⟨c, h⟩ := range_of_triangle u b hΦ hu h j hv'
    exact Or.inr ⟨c, Or.inl h⟩
  · have hv' : v (j + 1) = -v (j - 1) := eq_neg_of_add_eq_zero_left
      (by rw [add_comm]; rw [hj, zero_smul] at hv; exact hv)
    obtain ⟨c, e, he, h⟩ := range_hirzebruch_of_opposite u b hΦ hu h hv'
    exact Or.inr ⟨c, Or.inr ⟨e, he, h⟩⟩

end TauCeti.Toric.Fan
