/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Minimal
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Fan.StarSubdivision.Contraction

/-!
# Reduction to a minimal complete regular fan

The ray classification and the inverse star-subdivision construction give a
finite sequence of toric contractions from any regular complete rank-two fan
to a fan with the rays of the projective plane or of a minimal Hirzebruch
surface. Each step drops a ray.
-/

public section

open Module

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- Every regular complete rank-two fan is obtained from a complete regular fan
in projective-plane or minimal Hirzebruch normal form by a finite chain of
star subdivisions at two-ray cones on the same lattice. -/
theorem exists_starSubdivision_chain_from_minimal
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) :
    ∃ Ψ : Fan i, Ψ.IsRegular ∧ Ψ.IsComplete ∧
      Relation.ReflTransGen IsTwoRayStarSubdivision Ψ Φ ∧
      ∃ c : Basis (Fin 2) ℤ N,
        Set.range (Ray.primitiveGenerator (Phi := Ψ)) = {c 0, c 1, -c 0 - c 1} ∨
        ∃ e : ℕ, e ≠ 1 ∧ Set.range (Ray.primitiveGenerator (Phi := Ψ)) =
          {c 0, c 1, -c 0, (e : ℤ) • c 0 - c 1} := by
  classical
  induction hn : Nat.card Φ.Ray using Nat.strong_induction_on generalizing Φ with
  | ind n ih =>
    rcases exists_ray_eq_sum_or_exists_basis_ray_generators b hΦ hc with
      ⟨p, r, q, hp, hq, hr⟩ | hnormal
    · obtain ⟨Ξ, hΞ, σ, hσ, hΞc, hstar, -, hnmem, -⟩ :=
        exists_star_subdivision_of_ray_eq_sum b hΦ hc hp hq hr
      have hstep : IsTwoRayStarSubdivision Ξ Φ := hstar ▸ .along hΞ σ hσ
      let f := hstep.isSubdivision.liftRay
      have hinj : Function.Injective f := by
        intro x y hxy
        apply Ray.primitiveGenerator_injective
        simpa only [f, IsSubdivision.primitiveGenerator_liftRay] using
          congrArg Ray.primitiveGenerator hxy
      have hnsurj : ¬ Function.Surjective f := by
        intro hs
        obtain ⟨x, hx⟩ := hs r
        have hcone := congrArg (fun t : Φ.Ray ↦ t.toCone.val) hx
        dsimp only [f] at hcone
        rw [IsSubdivision.liftRay_toCone] at hcone
        exact hnmem (hcone ▸ x.toCone.property)
      let := Fintype.ofFinite Ξ.Ray
      let := Fintype.ofFinite Φ.Ray
      have hlt : Nat.card Ξ.Ray < n := by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_injective_not_surjective f hinj hnsurj
      obtain ⟨Ψ, hΨ, hΨc, hchain, hb⟩ := ih _ hlt hΞ hΞc rfl
      exact ⟨Ψ, hΨ, hΨc, hchain.tail hstep, hb⟩
    · exact ⟨Φ, hΦ, hc, .refl, hnormal⟩

end TauCeti.Toric.Fan
