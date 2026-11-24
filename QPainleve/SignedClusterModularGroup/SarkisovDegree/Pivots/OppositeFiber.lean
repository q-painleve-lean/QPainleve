/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Pivots

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# High base orders on the opposite invariant fiber

In a logarithmic Hirzebruch resolution with a high center on the open orbit of
one invariant fiber, low orders on the open section orbits force every other high
order to lie over a single proper point on the opposite fiber. At a smooth point
of that fiber there is exactly one high step. The corner case records the first
step and the projected point of every infinitely near high step. This supplies
the pivot location after the quadric preparation in Case C of
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pt" => IsLocalRing.closedPoint ℂ
local notation "center[" ρ "," c "]" => Fan.Ray.binomialCenter ρ rankTwo
  (b.detDualEquiv_self (Fan.Ray.primitiveGenerator ρ)) (Fan.Ray.surjective_detCharacter ρ b) c pt

variable {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)
  (hg : g ≫ (P ↘ S) = T.toBase ≫ (Φ.algebraicRealization ↘ S))

include hg in
/-- Suppose a logarithmic Hirzebruch resolution has a high order over the open
orbit of the first invariant fiber, and the first orders over both open section
orbits are at most half the ruling degree. Either the selected step is the
only high step or all other high steps project to a single point on the opposite
fiber. The first step over that point is high. If the point is on the open orbit
of the opposite fiber, its first step accounts for every other high order. -/
theorem high_base_orders_on_opposite_hirzebruch_fiber :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking (k := ℂ) hT f).symm (Additive.ofMul (pullback g H))
    let β := (Φ.hirzebruchPicardBasis b e hΦ r hr).repr v.1 1
    (Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    (∀ (k : Fin n), (∀ a < k, hT.baseCenter a ≠ hT.baseCenter k) →
      ∀ (s : Fin 2) (c : ℂˣ), hT.baseCenter k = center[r ((![0, 2] : Fin 2 → Fin 4) s),c] →
      2 * (-v.2 k) ≤ β) →
    ∀ (c : ℂˣ) (j : Fin n), hT.baseCenter j = center[r 1,c] → β < 2 * (-v.2 j) →
      (∀ k, β < 2 * (-v.2 k) → k = j) ∨
      ∃ l : Fin n, l ≠ j ∧ β < 2 * (-v.2 l) ∧
        (∀ a < l, hT.baseCenter a ≠ hT.baseCenter l) ∧
        (∀ k, k ≠ j → β < 2 * (-v.2 k) → hT.baseCenter k = hT.baseCenter l) ∧
        ((∃ σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
          hT.baseCenter l = Φ.distinguishedPointHom σ pt ∧ (r 3).toCone ≤ σ) ∨
        (∃ c' : ℂˣ, hT.baseCenter l = center[r 3,c'] ∧
          ∀ k, k ≠ j → β < 2 * (-v.2 k) → k = l)) := by
  classical
  intro hcones hdim hnoeth v β hlog hsection c j hj hjhigh
  let := hcones
  let := hdim
  let := hnoeth
  let high (k : Fin n) := β < 2 * (-v.2 k)
  have high_of_le {k l : Fin n} (hk : high k) (hle : -v.2 k ≤ -v.2 l) : high l :=
    hk.trans_le (mul_le_mul_of_nonneg_left hle (by decide))
  by_cases h : ∃ k, k ≠ j ∧ high k
  · obtain ⟨k, hkj, hk⟩ := h
    have first {k : Fin n} (hne : k ≠ j) (hk : high k) :=
      hT.exists_first_high_baseCenter_of_high_base_order_on_hirzebruch_fiber b e hΦ hc r hr g hg
        hlog c hj hjhigh hk hne
    have hopen (a : ℂˣ) : center[r 3,a] ∈ (Φ.rayBoundaryIdeal hΦ (r 3)).support :=
      ((r 3).binomialCenter_mem_support_sdiff_colon hΦ rankTwo (b.detDualEquiv_self _)
        ((r 3).surjective_detCharacter b) a).1
    have hopp {k : Fin n} (hne : k ≠ j) (hk : high k) :
        hT.baseCenter k ∈ (Φ.rayBoundaryIdeal hΦ (r 3)).support := by
      obtain ⟨l, hl, hlfirst, -, hle, hcorner | ho | hs⟩ := first hne hk
      · obtain ⟨σ, -, hpoint, hface⟩ := hcorner
        rw [← hl, hpoint]
        exact (Φ.distinguishedPoint_mem_support_rayBoundaryIdeal_iff hΦ σ (r 3)).mpr hface
      · obtain ⟨a, ha⟩ := ho
        rw [← hl, ha]
        exact hopen a
      · obtain ⟨t, a, ha⟩ := hs
        exact (not_lt_of_ge (hsection l hlfirst t a ha) (high_of_le hk hle)).elim
    obtain ⟨l, -, hlfirst, hlne, hle, hcases⟩ := first hkj hk
    have hlj : l ≠ j := fun h ↦ hlne (congrArg hT.baseCenter h)
    have hl : high l := high_of_le hk hle
    refine Or.inr ⟨l, hlj, hl, hlfirst, ?_, ?_⟩
    · intro q hqj hq
      exact hT.baseCenter_eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
        1 (hopp hqj hq) (hopp hlj hl) hq hl
    · rcases hcases with hcorner | ⟨a, ha⟩ | ⟨t, a, ha⟩
      · exact Or.inl hcorner
      · exact Or.inr ⟨a, ha, fun q hqj hq ↦
          (hT.eq_of_high_base_orders_on_hirzebruch_fiber b e hΦ hc r hr g hg
            hlog 1 a ha (hopp hqj hq) hl hq).symm⟩
      · exact (not_lt_of_ge (hsection l hlfirst t a ha) hl).elim
  · exact Or.inl (fun k hk ↦ by by_contra hne; exact h ⟨k, hne, hk⟩)

end QPainleve.BlowupTower.IsClosedPointTower
