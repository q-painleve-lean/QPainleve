/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import Mathlib.Data.ZMod.Basic

/-!
# Reconstruction of a toric surface fan from its boundary

The cyclically ordered self-intersections of the prime boundary divisors of a smooth
projective toric surface determine its fan. An adjacent pair gives a lattice basis, and
the boundary recurrence determines every subsequent ray. The resulting lattice
equivalence also transports the cones and respects the given ray numbering.

This is the fan comparison used in Gross–Hacking–Keel,
*Moduli of surfaces with an anti-canonical cycle*, Remark 2.4.
-/

public section

open PointedCone
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

namespace Fan

variable {n : ℕ}

private theorem adjacent_iff (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (u : ZMod n ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (j : ZMod n) (τ : Φ.Ray) :
    (u j ≠ τ ∧ ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ τ.toCone ≤ σ) ↔
      τ = u (j - 1) ∨ τ = u (j + 1) := by
  exact ray_neighbors_iff_of_det b hΦ hc
    (by simpa only [sub_add_cancel] using hu (j - 1)) (hu j) τ

private theorem mem_cones_iff (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (u : ZMod n ≃ Φ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    {σ : PointedCone ℝ V} :
    σ ∈ Φ.cones ↔ σ = ⊥ ∨ σ ∈ Set.range (fun j ↦ (u j).toCone.val) ∨
      σ ∈ Set.range (fun j ↦ (u j).toCone.val ⊔ (u (j + 1)).toCone.val) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  constructor
  · intro hσ
    by_cases hzero : σ = ⊥
    · exact Or.inl hzero
    let s : Φ.cones := ⟨σ, hσ⟩
    obtain ⟨ρ, hρ⟩ := Φ.exists_ray_le_of_ne_bot s hzero
    obtain ⟨j, rfl⟩ := u.surjective ρ
    by_cases htwo : ∃ τ : Φ.Ray, u j ≠ τ ∧ τ.toCone ≤ s
    · obtain ⟨τ, hne, hτ⟩ := htwo
      have hsup := cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ
      rcases (adjacent_iff b hΦ hc u hu j τ).mp ⟨hne, s, hρ, hτ⟩ with rfl | rfl
      · exact Or.inr (Or.inr ⟨j - 1, by simpa [sup_comm] using hsup.symm⟩)
      · exact Or.inr (Or.inr ⟨j, hsup.symm⟩)
    · have he : s = (u j).toCone := by
        refine le_antisymm (Φ.le_iff_forall_ray_le.mpr fun τ hτ ↦ ?_) hρ
        by_contra hn
        exact htwo ⟨τ, fun he ↦ hn (he ▸ le_rfl), hτ⟩
      exact Or.inr (Or.inl ⟨j, (congrArg Subtype.val he).symm⟩)
  · rintro (rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Φ.bot_mem (u 0).toCone.property
    · exact (u j).toCone.property
    · obtain ⟨s, hρ, hτ⟩ := (hu j).2
      have hne : u j ≠ u (j + 1) := by
        intro he
        have hd := (hu j).1
        rw [← he, b.detDualEquiv_self] at hd
        omega
      simpa only [cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ] using s.property

private theorem map_mem_cones_iff
    (f : V ≃ₗ[ℝ] V') (u : ZMod n ≃ Φ.Ray) (v : ZMod n ≃ Ψ.Ray)
    (hu : ∀ σ, σ ∈ Φ.cones ↔ σ = ⊥ ∨ σ ∈ Set.range (fun j ↦ (u j).toCone.val) ∨
      σ ∈ Set.range (fun j ↦ (u j).toCone.val ⊔ (u (j + 1)).toCone.val))
    (hv : ∀ σ, σ ∈ Ψ.cones ↔ σ = ⊥ ∨ σ ∈ Set.range (fun j ↦ (v j).toCone.val) ∨
      σ ∈ Set.range (fun j ↦ (v j).toCone.val ⊔ (v (j + 1)).toCone.val))
    (hf : ∀ j, PointedCone.map (f : V →ₗ[ℝ] V') (u j).toCone.val = (v j).toCone.val)
    (σ : PointedCone ℝ V) :
    PointedCone.map (f : V →ₗ[ℝ] V') σ ∈ Ψ.cones ↔ σ ∈ Φ.cones := by
  have hinj : Function.Injective (PointedCone.map (f : V →ₗ[ℝ] V')) :=
    Submodule.map_injective_of_injective f.injective
  have hs (j : ZMod n) :
      PointedCone.map (f : V →ₗ[ℝ] V') ((u j).toCone.val ⊔ (u (j + 1)).toCone.val) =
        (v j).toCone.val ⊔ (v (j + 1)).toCone.val := by
    simp only [PointedCone.map] at hf ⊢
    rw [Submodule.map_sup, hf, hf]
  rw [hu, hv]
  have hbot : PointedCone.map (f : V →ₗ[ℝ] V') ⊥ = ⊥ := Submodule.map_bot _
  simp only [Set.mem_range, ← hs, ← hbot]
  simp only [← hf, hinj.eq_iff]

private theorem map_primitiveGenerator_of_selfIntersection_eq
    [NeZero n]
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (u : ZMod n ≃ Φ.Ray) (v : ZMod n ≃ Ψ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (hv : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (hself : ∀ j, Φ.rayBoundarySelfIntersection hΦ (u j) = Ψ.rayBoundarySelfIntersection hΨ (v j))
    (f : N ≃ₗ[ℤ] N') (h₀ : f (u 0).primitiveGenerator = (v 0).primitiveGenerator)
    (h₁ : f (u 1).primitiveGenerator = (v 1).primitiveGenerator) :
    ∀ j, f (u j).primitiveGenerator = (v j).primitiveGenerator := by
  have hstep (j : ZMod n)
      (hprev : f (u (j - 1)).primitiveGenerator = (v (j - 1)).primitiveGenerator)
      (hcur : f (u j).primitiveGenerator = (v j).primitiveGenerator) :
      f (u (j + 1)).primitiveGenerator = (v (j + 1)).primitiveGenerator := by
    have h := primitiveGenerator_add_selfIntersection_smul_add_eq_zero b hΦ hc
      (by simpa only [sub_add_cancel] using hu (j - 1)) (hu j)
    have h' := primitiveGenerator_add_selfIntersection_smul_add_eq_zero b' hΨ hc'
      (by simpa only [sub_add_cancel] using hv (j - 1)) (hv j)
    have hf := congrArg f h
    simp only [map_add, map_smul, map_zero, hprev, hcur, hself] at hf
    exact add_left_cancel (hf.trans h'.symm)
  have hn (k : ℕ) : (f (u (k : ZMod n)).primitiveGenerator = (v (k : ZMod n)).primitiveGenerator) ∧
      f (u ((k : ZMod n) + 1)).primitiveGenerator = (v ((k : ZMod n) + 1)).primitiveGenerator := by
    induction k with
    | zero => simpa using And.intro h₀ h₁
    | succ k ih =>
      simp only [Nat.cast_succ]
      exact ⟨ih.2, hstep ((k : ZMod n) + 1) (by simpa only [add_sub_cancel_right] using ih.1) ih.2⟩
  exact ZMod.natCast_zmod_surjective.forall.mpr fun k ↦ (hn k).1

private theorem exists_basis_of_first_two_rays (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) {ρ τ : Φ.Ray}
    (h : b.detDualEquiv ρ.primitiveGenerator τ.primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, ρ.toCone ≤ σ ∧ τ.toCone ≤ σ) :
    ∃ a : Module.Basis (Fin 2) ℤ N, a 0 = ρ.primitiveGenerator ∧ a 1 = τ.primitiveGenerator := by
  obtain ⟨hdet, σ, hρ, hτ⟩ := h
  have hne : ρ ≠ τ := by
    intro he
    rw [he, b.detDualEquiv_self] at hdet
    omega
  exact exists_basis_of_ray_ne_of_le ((isRegular_iff.1 hΦ) _ σ.property)
    (by simpa using Module.finrank_eq_card_basis b) hne hρ hτ

/-- If two complete regular rank-two fans with projective realizations have equal cyclically
numbered boundary self-intersections, there is a unique fan equivalence matching the ray
numberings. The determinant and cone conditions specify the two cyclic orders. -/
theorem existsUnique_fanEquiv_of_boundarySelfIntersections
    [NeZero n]
    [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (u : ZMod n ≃ Φ.Ray) (v : ZMod n ≃ Ψ.Ray)
    (hu : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ)
    (hv : ∀ j, b'.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (hself : ∀ j, Φ.rayBoundarySelfIntersection hΦ (u j) = Ψ.rayBoundarySelfIntersection hΨ (v j)) :
    ∃! e : FanEquiv Φ Ψ, ∀ j, e.rayEquiv (u j) = v j := by
  obtain ⟨a, ha₀, ha₁⟩ :=
    exists_basis_of_first_two_rays b hΦ (by simpa only [zero_add] using hu 0)
  obtain ⟨a', ha₀', ha₁'⟩ :=
    exists_basis_of_first_two_rays b' hΨ (by simpa only [zero_add] using hv 0)
  let f := a.equiv a' (Equiv.refl (Fin 2))
  have hf (k : Fin 2) : f (a k) = a' k := a.equiv_apply _ _ _
  let A := Φ.lattice.isBaseChange.basis a
  let A' := Ψ.lattice.isBaseChange.basis a'
  let g := A.equiv A' (Equiv.refl (Fin 2))
  have hgl : ∀ x, g (i x) = i' (f x) := by
    have hg : g.toLinearMap = Φ.lattice.extend i' f.toAddEquiv := by
      apply A.ext
      intro k
      rw [LinearEquiv.coe_coe, A.equiv_apply, Equiv.refl_apply]
      simp only [A, A', IsBaseChange.basis_apply, AddMonoidHom.coe_toIntLinearMap,
        IsIntegralLattice.extend_apply]
      exact congrArg i' (hf k).symm
    intro x
    rw [← LinearEquiv.coe_coe, hg, IsIntegralLattice.extend_apply]
    rfl
  have hfg := map_primitiveGenerator_of_selfIntersection_eq b b' hΦ hΨ hc hc' u v hu hv hself f
    (by rw [← ha₀, ← ha₀', hf]) (by rw [← ha₁, ← ha₁', hf])
  have hray (j : ZMod n) :
      PointedCone.map (g : V →ₗ[ℝ] V') (u j).toCone.val = (v j).toCone.val := by
    rw [Ray.toCone_eq_hull_primitiveGenerator, Ray.toCone_eq_hull_primitiveGenerator,
      PointedCone.map, Submodule.map_span, Set.image_singleton]
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hgl, hfg]
  let e : FanEquiv Φ Ψ :=
    ⟨f.toAddEquiv, g, hgl, map_mem_cones_iff g u v
      (fun _ ↦ mem_cones_iff b hΦ hc u hu) (fun _ ↦ mem_cones_iff b' hΨ hc' v hv) hray⟩
  refine ⟨e, fun j ↦ Ray.primitiveGenerator_injective (by simpa [e] using hfg j), ?_⟩
  intro e' he'
  apply FanEquiv.ext
  have hk (j : ZMod n) := congrArg Ray.primitiveGenerator (he' j)
  simp only [FanEquiv.primitiveGenerator_rayEquiv] at hk
  have hEq : e'.latticeEquiv.toIntLinearEquiv.toLinearMap = f.toLinearMap := by
    apply a.ext
    simp only [LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv, hf, Fin.forall_fin_two]
    exact ⟨by simpa only [ha₀, ha₀'] using hk 0, by simpa only [ha₁, ha₁'] using hk 1⟩
  exact AddEquiv.ext fun x ↦ DFunLike.congr_fun hEq x

end Fan

end TauCeti.Toric
