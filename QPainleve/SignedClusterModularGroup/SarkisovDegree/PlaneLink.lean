/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Sarkisov degree for links from the plane

Blowing up a center of order `m` in a plane system of degree `d` gives ruling
coordinates `(d, d - m)` on the first Hirzebruch surface. For a center on the
interior of a boundary edge, first blow up the opposite vertex, perform the
elementary transformation at the edge center, then exchange the rulings on the
quadric. The resulting fiber degree is again `d - m`. We transport the two
homaloidal identities, including the remaining base orders, for both blocks.

The bidegree decrease is the plane case of Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open Prod.Lex

namespace QPainleve

/-- The Sarkisov bidegree of a plane system with degree `d` and total base order `M`.
The first coordinate is six times the Sarkisov degree. -/
def planeSarkisovBidegree (d M : ℕ) : ℕ ×ₗ ℕ := toLex (2 * d, M)

@[simp]
theorem ofLex_planeSarkisovBidegree (d M : ℕ) :
    ofLex (planeSarkisovBidegree d M) = (2 * d, M) := (rfl)

variable {ι : Type*} [Fintype ι] {d : ℤ} {m : ι → ℤ}

/-- Each base order is strictly less than the degree of a positive-degree plane system
satisfying the square homaloidal identity. -/
theorem baseOrder_lt_degree_of_plane_homaloidal (hd : 0 < d) (j : ι)
    (hsq : ∑ i, m i ^ 2 = d ^ 2 - 1) : m j < d := by
  have hbound : m j ^ 2 ≤ ∑ i, m i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg (m i)) (Finset.mem_univ j)
  rw [hsq] at hbound
  by_contra! hj
  nlinarith only [hbound, mul_nonneg (sub_nonneg.mpr hj) (by omega : 0 ≤ m j + d)]

variable [DecidableEq ι]

/-- In the marking by fiber and negative section on the first Hirzebruch surface,
blowing up a plane point of order `m p` changes the degree coordinates to
`(d, d - m p)` and removes the selected order. The two homaloidal identities
are equivalent before and after this change of marking. -/
theorem homaloidal_identities_plane_blowup (p : ι) :
    let m' := Function.update m p 0
    ((∑ i, m i ^ 2) = d ^ 2 - 1 ∧ (∑ i, m i) = 3 * d - 3) ↔
      ((∑ i, m' i ^ 2) = 2 * d * (d - m p) - (d - m p) ^ 2 - 1 ∧
        (∑ i, m' i) = 2 * d + (d - m p) - 3) := by
  dsimp only
  simp_rw [Function.apply_update (fun _ (x : ℤ) ↦ x ^ 2) m p 0, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ p), Finset.sum_update_of_mem (Finset.mem_univ p)]
  simp only [Finset.sdiff_singleton_eq_erase,
    Finset.sum_erase_eq_sub (Finset.mem_univ p)]
  constructor <;> rintro ⟨hsq, hsum⟩ <;> constructor
  · nlinarith only [hsq]
  · omega
  · nlinarith only [hsq]
  · omega

/-- For the edge-center block, the first blowup at the opposite vertex `p` removes
its order. The transform at `q` replaces that order by `d - m p - m q`, the
order at the reverse center. After swapping the quadric rulings, the coefficients
are `(d - m p, d - m q)`, and both homaloidal identities hold for these data. -/
theorem homaloidal_identities_plane_edgeLink {p q : ι} (hpq : p ≠ q)
    (hsq : ∑ i, m i ^ 2 = d ^ 2 - 1) (hsum : ∑ i, m i = 3 * d - 3) :
    let m' := Function.update (Function.update m p 0) q (d - m p - m q)
    (∑ i, m' i ^ 2) = 2 * (d - m p) * (d - m q) - 1 ∧
      (∑ i, m' i) = 2 * (d - m p) + 2 * (d - m q) - 3 := by
  obtain ⟨hsq', hsum'⟩ := (homaloidal_identities_plane_blowup (d := d) (m := m) p).mp ⟨hsq, hsum⟩
  have hsum₁ : (∑ i, Function.update m p 0 i) = 2 * d + (2 - (1 : ℤ)) * (d - m p) - 3 := by
    simpa using hsum'
  have h := homaloidal_identities_elementaryTransform (e := 1) false q
    (by simpa only [one_mul] using hsq') hsum₁
  dsimp only at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte, sub_self, zero_mul, sub_zero,
    Function.update_of_ne hpq.symm] at h
  exact ⟨by nlinarith only [h.1], by linarith only [h.2]⟩

omit [DecidableEq ι] in
/-- Either plane link at an order strictly greater than `d / 3` reduces the
first coordinate of the Sarkisov bidegree. The new degree is positive, and
the comparison holds for the actual total orders regardless of their change. -/
theorem hirzebruchSarkisovBidegree_lt_plane_of_high_order (hd : 0 < d) (j : ι)
    (hsq : ∑ i, m i ^ 2 = d ^ 2 - 1) (hhigh : d < 3 * m j) (M M' : ℕ) :
    0 < d - m j ∧
      hirzebruchSarkisovBidegree (d - m j).toNat M' < planeSarkisovBidegree d.toNat M := by
  have hm := baseOrder_lt_degree_of_plane_homaloidal hd j hsq
  refine ⟨by omega, ?_⟩
  rw [← toLex_ofLex (hirzebruchSarkisovBidegree _ _), ofLex_hirzebruchSarkisovBidegree]
  apply Prod.Lex.toLex_lt_toLex.mpr
  exact Or.inl (by omega)

end QPainleve
