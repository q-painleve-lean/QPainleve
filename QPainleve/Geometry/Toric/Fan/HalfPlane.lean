/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.Determinant.Dual
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic

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

/-- If both rays of the kernel line belong to a fan, every cone lies in one of the two
closed half-spaces of the functional. -/
theorem Fan.nonneg_or_nonpos_on_cone (Φ : Fan i) {f : V →ₗ[ℝ] ℝ} {v : V}
    (hker : f.ker = ℝ ∙ v) (hpos : hull ℝ {v} ∈ Φ.cones)
    (hneg : hull ℝ {-v} ∈ Φ.cones) (σ : Φ.cones) :
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
  have hRay : ∃ w : V, hull ℝ {w} ∈ Φ.cones ∧ f w = 0 ∧ z ∈ hull ℝ {w} := by
    rcases le_total 0 r with h | h
    · exact ⟨v, hpos, hfv, mem_hull_singleton.mpr ⟨r, h, hr⟩⟩
    · refine ⟨-v, hneg, by simp [hfv], mem_hull_singleton.mpr ⟨-r, neg_nonneg.mpr h, ?_⟩⟩
      simpa using hr
  obtain ⟨w, hw, hfw, hzw⟩ := hRay
  -- A face containing the combination must contain both points.
  have hface := Φ.inf_isFaceOf_left σ.property hw
  have hxw := (Submodule.mem_inf.mp (hface.mem_of_smul_add_smul_mem_left hx hy
    (neg_pos.mpr hyneg) hxpos (Submodule.mem_inf.mpr ⟨hz, hzw⟩))).2
  obtain ⟨a, -, rfl⟩ := mem_hull_singleton.mp hxw
  rw [map_smul, hfw, smul_zero] at hxpos
  exact (lt_irrefl 0) hxpos

/-- In rank two the real determinant character of a nonzero vector vanishes on its line. -/
theorem IsIntegralLattice.ker_realCharacter_detDualEquiv (hi : IsIntegralLattice i)
    (b : Module.Basis (Fin 2) ℤ N) {v : N} (hv : v ≠ 0) :
    (hi.realCharacter (b.detDualEquiv v).toAddMonoidHom).ker = ℝ ∙ i v := by
  let f := hi.realCharacter (b.detDualEquiv v).toAddMonoidHom
  have hf : f ≠ 0 := by
    intro hf
    have hzero : (b.detDualEquiv v).toAddMonoidHom = 0 :=
      hi.realCharacter_injective (hf.trans (map_zero hi.realCharacter).symm)
    exact hv (b.detDualEquiv.map_eq_zero_iff.mp (LinearMap.toAddMonoidHom_injective hzero))
  have := hi.finiteDimensional
  have hdim : Module.finrank ℝ V = 2 := by
    rw [← hi.finrank_eq, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  dsimp only [f] at hker
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    have hvv := b.det.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)
    simpa [f, IsIntegralLattice.realCharacter_apply, Module.Basis.detDualEquiv_apply] using hvv
  · rw [finrank_span_singleton (fun h ↦ hv (hi.injective (h.trans (map_zero i).symm)))]
    omega

namespace Fan

variable (Φ : Fan i)

/-- The determinant character of a nonzero lattice vector has constant weak sign on each
cone whenever the fan contains the two opposite rays in that direction. -/
theorem detCharacter_nonneg_or_nonpos (b : Module.Basis (Fin 2) ℤ N) {v : N}
    (hv : v ≠ 0) (hpos : PointedCone.hull ℝ {i v} ∈ Φ.cones)
    (hneg : PointedCone.hull ℝ {i (-v)} ∈ Φ.cones) (σ : Φ.cones) :
    (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter (b.detDualEquiv v).toAddMonoidHom x ≤ 0 :=
  Φ.nonneg_or_nonpos_on_cone (Φ.lattice.ker_realCharacter_detDualEquiv b hv)
    hpos (by simpa only [map_neg] using hneg) σ

end Fan

end TauCeti.Toric
