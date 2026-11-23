/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.DeterminantCharacters
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

import TauCeti.Data.Fin.Rev

/-!
# Fans cut by a line

A linear functional whose kernel is covered by two opposite rays of a fan has constant
weak sign on each cone. In rank two the real extension of the determinant character in
a nonzero lattice direction has this kernel. This lets one use the two half-planes as
domains for toric morphisms and piecewise linear transformations.
-/

public section

namespace TauCeti.Toric

open PointedCone

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- If each ray of the kernel line belongs to the fan whenever its generator lies in the
support, every cone lies in one of the two closed half-spaces of the functional. -/
theorem Fan.nonneg_or_nonpos_on_cone_of_mem_support (Φ : Fan i) {f : V →ₗ[ℝ] ℝ} {v : V}
    (hker : f.ker = ℝ ∙ v) (hpos : v ∈ Φ.support → hull ℝ {v} ∈ Φ.cones)
    (hneg : -v ∈ Φ.support → hull ℝ {-v} ∈ Φ.cones) (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ f x) ∨ ∀ x ∈ σ.val, f x ≤ 0 := by
  by_cases hs : ∀ x ∈ σ.val, 0 ≤ f x
  · exact Or.inl hs
  right
  push Not at hs
  obtain ⟨y, hy, hyneg⟩ := hs
  intro x hx
  by_contra! hxpos
  -- A positive combination of the two points lies on one of the opposite rays.
  let z := (-f y) • x + f x • y
  have hz : z ∈ σ.val := σ.val.add_mem (σ.val.smul_mem (neg_pos.mpr hyneg).le hx)
    (σ.val.smul_mem hxpos.le hy)
  have hzf : z ∈ f.ker := LinearMap.mem_ker.mpr (by simp [z, mul_comm])
  rw [hker] at hzf
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hzf
  have hfv : f v = 0 :=
    LinearMap.mem_ker.mp (hker.symm ▸ Submodule.mem_span_singleton_self v)
  have hr₀ : r ≠ 0 := by
    intro h
    have hzero : z = 0 := by simpa [h] using hr.symm
    have hsal := (Φ.isToricCone σ.property).salient
    apply hsal ((-f y) • x) (σ.val.smul_mem (neg_pos.mpr hyneg).le hx)
      (smul_ne_zero (neg_pos.mpr hyneg).ne' (fun e ↦ hxpos.ne' (by simp [e])))
    rw [← neg_eq_of_add_eq_zero_left hzero, neg_neg]
    exact σ.val.smul_mem hxpos.le hy
  have hRay : ∃ w : V, hull ℝ {w} ∈ Φ.cones ∧ f w = 0 ∧ z ∈ hull ℝ {w} := by
    have aux {a : ℝ} {w : V} (ha : 0 < a) (hw : a • w = z)
        (hm : w ∈ Φ.support → hull ℝ {w} ∈ Φ.cones) (hf : f w = 0) :
        ∃ w : V, hull ℝ {w} ∈ Φ.cones ∧ f w = 0 ∧ z ∈ hull ℝ {w} := by
      have hmem := (σ.val.smul_mem_iff ha).mp (hw.symm ▸ hz)
      exact ⟨w, hm (Φ.subset_support σ.property hmem), hf,
        mem_hull_singleton.mpr ⟨a, ha.le, hw⟩⟩
    rcases lt_or_gt_of_ne hr₀ with h | h
    · exact aux (neg_pos.mpr h) (by simpa using hr) hneg (by simp [hfv])
    · exact aux h hr hpos hfv
  obtain ⟨w, hw, hfw, hzw⟩ := hRay
  -- A face containing the combination must contain both points.
  have hface := Φ.inf_isFaceOf_left σ.property hw
  have hxw := (Submodule.mem_inf.mp (hface.mem_of_smul_add_smul_mem_left hx hy
    (neg_pos.mpr hyneg) hxpos (Submodule.mem_inf.mpr ⟨hz, hzw⟩))).2
  obtain ⟨a, -, rfl⟩ := mem_hull_singleton.mp hxw
  rw [map_smul, hfw, smul_zero] at hxpos
  exact (lt_irrefl 0) hxpos

namespace Fan

variable (Φ : Fan i)

/-- The determinant character of a nonzero lattice vector has constant weak sign on each
cone whenever the fan contains the two opposite rays in that direction. -/
theorem detCharacter_nonneg_or_nonpos (b : Module.Basis (Fin 2) ℤ N) {v : N}
    (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
    (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones) (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0 :=
  Φ.nonneg_or_nonpos_on_cone_of_mem_support (Φ.lattice.ker_realCharacter_detDualEquiv b hv)
    (fun _ ↦ hpos) (fun _ ↦ by simpa only [map_neg] using hneg) σ

/-- Each real basis coordinate has constant weak sign on a cone when the fan contains
both directions of its kernel line that lie in the support. -/
theorem nonneg_or_nonpos_basis_repr_on_cone
    (b : Module.Basis (Fin 2) ℤ N) (j : Fin 2) (σ : Φ.cones)
    (hpos : i (b j.rev) ∈ Φ.support → hull ℝ {i (b j.rev)} ∈ Φ.cones)
    (hneg : i (-b j.rev) ∈ Φ.support → hull ℝ {i (-b j.rev)} ∈ Φ.cones) :
    let c := Φ.lattice.isBaseChange.basis b
    (∀ x ∈ σ.val, 0 ≤ c.repr x j) ∨ ∀ x ∈ σ.val, c.repr x j ≤ 0 := by
  let c := Φ.lattice.isBaseChange.basis b
  have hne : j ≠ j.rev := by fin_cases j <;> decide
  have hc : c j.rev = i (b j.rev) := IsBaseChange.basis_apply _ Φ.lattice.isBaseChange _
  have hker : (c.coord j).ker = ℝ ∙ c j.rev := by
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · have hz : c.repr x j = 0 := LinearMap.mem_ker.mp hx
      rw [← Set.image_singleton (f := c) (a := j.rev), c.mem_span_image]
      intro k hk
      rcases Fin.fin_two_eq_or_eq_rev j k with rfl | rfl
      · exact (Finsupp.mem_support_iff.mp hk hz).elim
      · exact Set.mem_singleton _
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      simp [hne]
  exact Φ.nonneg_or_nonpos_on_cone_of_mem_support hker
    (by simpa only [hc] using hpos) (by simpa only [hc, map_neg] using hneg) σ

end Fan

end TauCeti.Toric
