/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.CyclicOrder.Basic

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

open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

namespace Fan

variable {n : ℕ}

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
  have hfg := map_primitiveGenerator_of_selfIntersection_eq b b' hΦ hΨ hc hc' u v hu hv hself f
    (by rw [← ha₀, ← ha₀', hf]) (by rw [← ha₁, ← ha₁', hf])
  let e := fanEquivOfCyclicRays b b' hΦ hΨ hc hc' u v hu hv f.toAddEquiv hfg
  refine ⟨e, fun j ↦ Ray.primitiveGenerator_injective (by simpa [e] using hfg j), ?_⟩
  intro e' he'
  apply FanEquiv.ext
  have hk (j : ZMod n) := congrArg Ray.primitiveGenerator (he' j)
  simp only [FanEquiv.primitiveGenerator_rayEquiv] at hk
  have hEq : e'.latticeEquiv.toIntLinearEquiv.toLinearMap = f.toLinearMap := by
    apply a.ext
    simp only [LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv, hf, Fin.forall_fin_two]
    exact ⟨by simpa only [ha₀, ha₀'] using hk 0, by simpa only [ha₁, ha₁'] using hk 1⟩
  exact AddEquiv.ext fun x ↦ by
    simp only [e, fanEquivOfCyclicRays_latticeEquiv]
    exact DFunLike.congr_fun hEq x

end Fan

end TauCeti.Toric
