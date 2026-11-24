/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Equiv

import QPainleve.Geometry.Toric.Fan.Boundary.Reconstruction

/-!
# The ruling exchange of the toric quadric

On the Hirzebruch fan of index zero, exchanging the two lattice basis vectors
gives a toric involution that preserves the reduced boundary.

The ruling exchange is the toric change of model used in Lutz's appendix to
Hacking and Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*,
proof of Theorem 8.4](https://arxiv.org/abs/2005.05010v3).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "u" => Equiv.trans (RingEquiv.toEquiv (RingEquiv.symm (ZMod.finEquiv 4))) r
local notation "p" => (Equiv.subLeft (1 : ZMod 4))
local notation "b'" => b.reindex (Equiv.swap 0 1)
local notation "f" => b.equiv b (Equiv.swap 0 1)

include hr in
private theorem quadric_rayGenerator (j : ZMod 4) :
    ((u) j).primitiveGenerator = ![b 0, b 1, -b 0, -b 1] ((ZMod.finEquiv 4).symm j) := by
  simpa only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    zero_smul, zero_sub] using congrFun hr ((ZMod.finEquiv 4).symm j)

include hr in
private theorem quadric_det (j k : ZMod 4) :
    b.detDualEquiv ((u) j).primitiveGenerator ((u) k).primitiveGenerator =
      if k = j + 1 then 1 else if k = j - 1 then -1 else 0 := by
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 4).surjective j
  obtain ⟨k, rfl⟩ := (ZMod.finEquiv 4).surjective k
  simp only [quadric_rayGenerator b r hr, RingEquiv.symm_apply_apply,
    ← map_one (ZMod.finEquiv 4), ← map_add, ← map_sub, (ZMod.finEquiv 4).injective.eq_iff]
  let d : Matrix (Fin 4) (Fin 4) ℤ := !![0, 1, 0, -1; -1, 0, 1, 0; 0, -1, 0, 1; 1, 0, -1, 0]
  have hd (j k : Fin 4) : d j k = if k = j + 1 then 1 else if k = j - 1 then -1 else 0 := by
    fin_cases j <;> fin_cases k <;> decide
  rw [← hd j k]
  have hswap := b.detDualEquiv_swap (b 1) (b 0)
  rw [b.detDualEquiv_apply_basis_zero_one] at hswap
  fin_cases j <;> fin_cases k <;>
    norm_num [d, b.detDualEquiv_self,
      b.detDualEquiv_apply_basis_zero_one, hswap, -Basis.detDualEquiv_apply]

include hΦ hc hr in
private theorem quadric_cyclicRays (j : ZMod 4) :
    b.detDualEquiv ((u) j).primitiveGenerator ((u) (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ((u) j).toCone ≤ σ ∧ ((u) (j + 1)).toCone ≤ σ := by
  refine ⟨by rw [quadric_det b r hr, ite_eq_left rfl], ?_⟩
  obtain ⟨prev, next, -, hnext, hn⟩ := Φ.exists_ray_neighbors b hΦ hc ((u) j)
  obtain ⟨k, rfl⟩ := (u).surjective next
  rw [quadric_det b r hr] at hnext
  split at hnext
  · rename_i hk
    subst k
    exact ((hn _).mpr (Or.inr rfl)).2
  · split at hnext <;> omega

include hΦ hc hr in
private theorem quadric_cyclicRays_swap (j : ZMod 4) :
    (b').detDualEquiv (((p).trans (u)) j).primitiveGenerator
      (((p).trans (u)) (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (((p).trans (u)) j).toCone ≤ σ ∧ (((p).trans (u)) (j + 1)).toCone ≤ σ := by
  have hstep : p (j + 1) + 1 = p j := by simp [Equiv.subLeft_apply, sub_eq_add_neg, add_comm]
  obtain ⟨hd, σ, h₀, h₁⟩ := quadric_cyclicRays b hΦ hc r hr (p (j + 1))
  rw [hstep] at hd h₁
  refine ⟨?_, σ, h₁, h₀⟩
  simp only [Equiv.trans_apply] at hd ⊢
  rw [Basis.detDualEquiv_reindex_swap, LinearMap.neg_apply, b.detDualEquiv_swap, hd, neg_neg]

include hr in
private theorem quadric_swap_generator (j : ZMod 4) :
    (f).toAddEquiv (((u) j).primitiveGenerator) = (((p).trans (u)) j).primitiveGenerator := by
  obtain ⟨j, rfl⟩ := (ZMod.finEquiv 4).surjective j
  simp only [Equiv.trans_apply ((p)) (u), quadric_rayGenerator b r hr, Equiv.subLeft_apply,
    map_sub, map_one, RingEquiv.symm_apply_apply]
  have hp (j : Fin 4) : 1 - j = (![1, 0, 3, 2] : Fin 4 → Fin 4) j := by
    fin_cases j <;> decide
  rw [hp j]
  fin_cases j <;> norm_num [LinearEquiv.coe_toAddEquiv, Basis.equiv_apply]

include hΦ hc hr in
/-- Exchanging the basis directions of a regular complete Hirzebruch fan of index
zero is a fan automorphism. -/
def quadricRulingExchange : FanEquiv Φ Φ :=
  fanEquivOfCyclicRays b (b') hΦ hΦ hc hc (u) ((p).trans (u))
    (quadric_cyclicRays b hΦ hc r hr) (quadric_cyclicRays_swap b hΦ hc r hr)
    (f).toAddEquiv (quadric_swap_generator b r hr)

local notation "E" => quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))

/-- The ruling exchange acts on the lattice by transposing the two basis directions. -/
@[simp]
theorem quadricRulingExchange_latticeEquiv : (E).latticeEquiv = (f).toAddEquiv :=
  fanEquivOfCyclicRays_latticeEquiv ..

/-- The ruling exchange is its own inverse as a fan equivalence. -/
@[simp]
theorem quadricRulingExchange_symm : (E).symm = E := by
  apply FanEquiv.ext
  rw [FanEquiv.symm_latticeEquiv, quadricRulingExchange_latticeEquiv]
  have he : (f).symm.toLinearMap = (f).toLinearMap := by
    apply b.ext
    intro j
    simp [Basis.equiv_symm, Basis.equiv_apply]
  exact AddEquiv.ext fun x ↦ by
    have hx := DFunLike.congr_fun he x
    exact hx

/-- The algebraic ruling exchange is an involution. -/
@[reassoc (attr := simp)]
theorem quadricRulingExchange_algebraicMap_comp : τ ≫ τ = 𝟙 Φ.algebraicRealization := by
  simpa only [quadricRulingExchange_symm] using (E).algebraicMap_comp_symm

variable [Nonempty Φ.cones]

/-- The ruling exchange preserves the reduced toric boundary as a closed subscheme. -/
@[simp]
theorem comap_boundaryIdeal_quadricRulingExchange :
    (Φ.boundaryIdeal inferInstance).comap τ = Φ.boundaryIdeal inferInstance :=
  (E).comap_boundaryIdeal_algebraicMap _ _

omit [Nonempty Φ.cones] in
/-- On the cyclic ray indices, the ruling exchange reverses the cycle and sends
index zero to index one. -/
@[simp]
theorem quadricRulingExchange_rayEquiv (j : Fin 4) :
    (E).rayEquiv (r j) = r (1 - j) := by
  apply Ray.primitiveGenerator_injective
  rw [FanEquiv.primitiveGenerator_rayEquiv, quadricRulingExchange_latticeEquiv]
  have h := quadric_swap_generator b r hr ((ZMod.finEquiv 4) j)
  simpa only [Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
    RingEquiv.symm_apply_apply, Equiv.subLeft_apply, ← map_one (ZMod.finEquiv 4),
    ← map_sub] using h

end TauCeti.Toric.Fan
