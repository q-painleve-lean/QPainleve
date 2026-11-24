/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Basic

import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Elementary mutation of a Hirzebruch fan

A mutation at one of the two section rays of a Hirzebruch fan changes the
signed parameter by one. The sections are indexed by the original section
rays, and the image of the chosen fiber ray is the second vector of the new
lattice basis. This is the fan description of the elementary transformations
in Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*, Lemma 8.9](
https://arxiv.org/abs/2005.05010v3).
-/

public section

open Module PointedCone

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones)
  (e : ℤ) (u : Fin 4 ≃ Φ.Ray)
  (hu : (fun j ↦ (u j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "pivot" => Ray.primitiveGenerator ρ
local notation "r" => Φ.mutationFanRayEquiv b
  (Ray.primitiveGenerator_ne_zero ρ) (Ray.hull_primitiveGenerator_mem ρ) hOpp

include hu in
/-- In the order induced by the mutation ray correspondence, the result is in
Hirzebruch normal form with parameter `e + 1` for a pivot on ray zero and
`e - 1` for a pivot on ray two. The parameter is signed, so the statement
also applies to either section of the quadric. -/
theorem Ray.mutationFan_hirzebruch_ray_generators (onSection : Bool)
    (hρ : ρ = u (if onSection then 0 else 2)) :
    ∃ d : Basis (Fin 2) ℤ N,
      d 0 = b 0 ∧ d 1 = b 1 - (if onSection then 0 else b 0) ∧
      (fun j ↦ ((u.trans r) j).primitiveGenerator) =
        ![d 0, d 1, -d 0, (if onSection then e + 1 else e - 1) • d 0 - d 1] := by
  have h01 : b.detDualEquiv (b 0) (b 1) = 1 := b.detDualEquiv_apply_basis_zero_one
  have h10 : b.detDualEquiv (b 1) (b 0) = -1 := by
    rw [b.detDualEquiv_swap, h01]
  have h00 : b.detDualEquiv (b 0) (b 0) = 0 := b.detDualEquiv_self _
  have hray (j : Fin 4) := congrFun hu j
  cases onSection with
  | false =>
    have hv' : pivot = -b 0 := hρ ▸ hray 2
    let d := b.map (LinearEquiv.transvection (f := b.coord 1) (v := -b 0)
      (by simp [Basis.coord_apply]))
    have hd₀ : d 0 = b 0 := by
      rw [Basis.map_apply, LinearEquiv.transvection.apply]
      simp [Basis.coord_apply]
    have hd₁ : d 1 = b 1 - b 0 := by
      rw [Basis.map_apply, LinearEquiv.transvection.apply]
      simp [Basis.coord_apply, sub_eq_add_neg]
    refine ⟨d, hd₀, hd₁, funext fun j ↦ ?_⟩
    simp only [Equiv.trans_apply, mutationFanRayEquiv_primitiveGenerator, hv', hray,
      ← Basis.detDualEquiv_apply, hd₀, hd₁, Bool.false_eq_true, ↓reduceIte]
    fin_cases j <;> norm_num [-Basis.detDualEquiv_apply, h00, h10] <;> module
  | true =>
    have hv' : pivot = b 0 := hρ ▸ hray 0
    refine ⟨b, rfl, (sub_zero _).symm, funext fun j ↦ ?_⟩
    simp only [Equiv.trans_apply, mutationFanRayEquiv_primitiveGenerator, hv', hray,
      ← Basis.detDualEquiv_apply, ↓reduceIte]
    fin_cases j <;> norm_num [-Basis.detDualEquiv_apply, h00, h10]
    module

include hu in
/-- The chosen section of a Hirzebruch fan has the other section as its opposite ray. -/
theorem hull_neg_primitiveGenerator_mem_of_hirzebruch :
    hull ℝ {i (-(u 0).primitiveGenerator)} ∈ Φ.cones := by
  have h₀ : (u 0).primitiveGenerator = b 0 := congrFun hu 0
  have h₂ : (u 2).primitiveGenerator = -b 0 := congrFun hu 2
  rw [h₀, ← h₂]
  exact (u 2).hull_primitiveGenerator_mem

include hu in
/-- The section on ray two of a Hirzebruch fan has ray zero as its opposite ray. -/
theorem hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two :
    hull ℝ {i (-(u 2).primitiveGenerator)} ∈ Φ.cones := by
  have h₀ : (u 0).primitiveGenerator = b 0 := congrFun hu 0
  have h₂ : (u 2).primitiveGenerator = -b 0 := congrFun hu 2
  rw [h₂, neg_neg, ← h₀]
  exact (u 0).hull_primitiveGenerator_mem

include hu in
/-- Mutation at the chosen section increases the signed parameter by one
in the same lattice basis. -/
theorem Ray.mutationFan_hirzebruch_ray_generators_of_section_zero (hρ : ρ = u 0) :
    (fun j ↦ ((u.trans r) j).primitiveGenerator) =
      ![b 0, b 1, -b 0, (e + 1) • b 0 - b 1] := by
  obtain ⟨d, h₀, h₁, hd⟩ := ρ.mutationFan_hirzebruch_ray_generators b hOpp e u hu true hρ
  simpa only [h₀, h₁, ↓reduceIte, sub_zero] using hd

end TauCeti.Toric.Fan
