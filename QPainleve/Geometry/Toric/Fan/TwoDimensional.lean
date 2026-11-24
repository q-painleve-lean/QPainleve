/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Regular

import QPainleve.Geometry.Toric.Fan.Adjacency
import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Two-dimensional cones in regular fans

In a rank-two regular fan, a cone with two rays is maximal among the cones of
the fan. When the fan is complete, every cone is contained in one of these cones.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

variable {Φ : Fan i}

/-- A regular cone with two rays in a rank-two fan is maximal. -/
theorem eq_of_le_fullCone (hΦ : Φ.IsRegular) {σ τ : Φ.cones}
    (hN : Module.finrank ℤ N = 2) (hc : Nat.card (ToricRay σ.val) = 2) (h : σ ≤ τ) : σ = τ := by
  have hface := Φ.isFaceOf_of_le τ.property σ.property h
  have hτ := isRegular_iff.1 hΦ _ τ.property
  have := ToricRay.finite_of_fg (Φ.isToricCone σ.property).fg
  have := ToricRay.finite_of_fg hτ.fg
  let e := ToricRay.faceEmbedding hface
  let _ := Fintype.ofFinite (ToricRay σ.val)
  let _ := Fintype.ofFinite (ToricRay τ.val)
  have hcard : Fintype.card (ToricRay τ.val) ≤ Fintype.card (ToricRay σ.val) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc, ← hN]
    exact hτ.card_toricRay_le_finrank
  have hsurj := ((Fintype.bijective_iff_injective_and_card e).2
    ⟨e.injective, le_antisymm (Fintype.card_le_of_injective e e.injective) hcard⟩).2
  apply Subtype.ext
  refine le_antisymm h ?_
  rw [← (Φ.isToricCone τ.property).hull_primitiveGenerator Φ.lattice]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  obtain ⟨s, rfl⟩ := hsurj r
  rw [primitiveGenerator_faceEmbedding]
  exact s.val.isFaceOf.le (primitiveGenerator_mem Φ.lattice (Φ.isToricCone σ.property) s)

/-- In a complete regular rank-two fan, every cone lies in a two-ray cone. -/
theorem exists_le_cone_of_card_toricRay_eq_two (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (σ : Φ.cones) :
    ∃ υ : Φ.cones, σ ≤ υ ∧ Nat.card (ToricRay υ.val) = 2 := by
  classical
  by_cases h : ∃ ρ τ : Φ.Ray, ρ ≠ τ ∧ ρ.toCone ≤ σ ∧ τ.toCone ≤ σ
  · obtain ⟨ρ, τ, hne, hρ, hτ⟩ := h
    exact ⟨σ, le_rfl, Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim hne hρ hτ⟩
  have := Φ.lattice.free
  have := Φ.lattice.finite
  let b : Module.Basis (Fin 2) ℤ N := hdim ▸ Module.finBasis ℤ N
  have : Nontrivial N := Module.nontrivial_of_finrank_eq_succ (n := 1) hdim
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Φ.Ray, ∀ τ : Φ.Ray, τ.toCone ≤ σ → τ = ρ := by
    by_cases hs : ∃ ρ : Φ.Ray, ρ.toCone ≤ σ
    · obtain ⟨ρ, hρ⟩ := hs
      refine ⟨ρ, fun τ ht ↦ ?_⟩
      by_contra hne
      exact h ⟨τ, ρ, hne, ht, hρ⟩
    · obtain ⟨ρ⟩ := Φ.nonempty_ray_of_isComplete hc
      exact ⟨ρ, fun τ ht ↦ (hs ⟨τ, ht⟩).elim⟩
  obtain ⟨_, next, -, -, hneighbors⟩ := Φ.exists_ray_neighbors b hΦ hc ρ
  obtain ⟨hne, υ, hρυ, hnext⟩ := (hneighbors next).mpr (Or.inr rfl)
  refine ⟨υ, Φ.le_iff_forall_ray_le.mpr (fun τ hτ ↦ ?_),
    Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hdim hne hρυ hnext⟩
  rw [hρ τ hτ]
  exact hρυ

private theorem mem_cones_of_range_primitiveGenerator_eq
    {Ψ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (hc : Ψ.IsComplete)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      Set.range (Ray.primitiveGenerator (Phi := Ψ)))
    {σ : Φ.cones} (hσ : Nat.card (ToricRay σ.val) = 2) : σ.val ∈ Ψ.cones := by
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hreg := isRegular_iff.mp hΦ _ σ.property
  obtain ⟨p, q, hp, hq, hd⟩ := exists_ray_pair_le_det_eq_one b hreg hσ
  have hpq : p ≠ q := by
    rintro rfl
    simp [b.detDualEquiv_self] at hd
  obtain ⟨p', hp'⟩ := hrays.le (Set.mem_range_self p)
  obtain ⟨q', hq'⟩ := hrays.le (Set.mem_range_self q)
  obtain ⟨t', ⟨ht', τ, hpt, htt⟩, -⟩ :=
    (exists_unique_ray_neighbor_on_each_side b hΨ hc p').1
  obtain ⟨t, ht⟩ := hrays.ge (Set.mem_range_self t')
  have hdt : b.detDualEquiv p.primitiveGenerator t.primitiveGenerator = 1 := by rwa [ht, ← hp']
  obtain ⟨c, hc₀, hc₁⟩ := exists_basis_of_ray_ne_of_le hreg hdim hpq hp hq
  let k := c.repr t.primitiveGenerator 0
  have hrepr := c.sum_repr t.primitiveGenerator
  rw [Fin.sum_univ_two, hc₀, hc₁] at hrepr
  have htcoord : c.repr t.primitiveGenerator 1 = 1 := by
    simpa only [map_add, map_zsmul, hd, hdt, b.detDualEquiv_self, smul_zero, zero_add,
      Int.zsmul_eq_mul, mul_one] using
      congrArg (b.detDualEquiv p.primitiveGenerator) hrepr
  have hsum : k • p.primitiveGenerator + q.primitiveGenerator = t.primitiveGenerator := by
    simpa only [k, htcoord, one_smul] using hrepr
  have hne : p' ≠ t' := fun h ↦ by simp [← h, b.detDualEquiv_self] at ht'
  have he : t = q := by
    -- The two candidate successors have determinant one with the same ray.
    -- The sign of their displacement puts one in the cone bounded by the other.
    rcases le_total 0 k with hk | hk
    · have hm : t.toCone ≤ σ := by
        rw [t.toCone_le_iff, ← hsum, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
        exact σ.val.add_mem (σ.val.smul_mem (by exact_mod_cast hk) (hp p.primitiveGenerator_mem))
          (hq q.primitiveGenerator_mem)
      exact (Φ.ray_eq_or_eq_of_le hreg hdim hpq hp hq hm).resolve_left (by
        rintro rfl
        simp [b.detDualEquiv_self] at hdt)
    · have hqsum : q'.primitiveGenerator = (-k) • p'.primitiveGenerator +
          t'.primitiveGenerator := by rw [hq', hp', ← ht, ← hsum, ← add_assoc, ← add_smul]; simp
      have hm : q'.toCone ≤ τ := by
        rw [q'.toCone_le_iff, hqsum, map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
        exact τ.val.add_mem (τ.val.smul_mem (by exact_mod_cast neg_nonneg.mpr hk)
          (hpt p'.primitiveGenerator_mem)) (htt t'.primitiveGenerator_mem)
      rcases Ψ.ray_eq_or_eq_of_le (isRegular_iff.mp hΨ _ τ.property) hdim hne hpt htt hm with h | h
      · exact (hpq (Ray.primitiveGenerator_injective (by rw [← hp', ← hq', h]))).elim
      · exact Ray.primitiveGenerator_injective (by rw [ht, ← h, hq'])
  have hpt' : p'.toCone.val = p.toCone.val := by
    rw [p'.toCone_eq_hull_primitiveGenerator, p.toCone_eq_hull_primitiveGenerator, hp']
  have htt' : t'.toCone.val = q.toCone.val := by
    rw [t'.toCone_eq_hull_primitiveGenerator, q.toCone_eq_hull_primitiveGenerator, ← ht, he]
  rw [cone_eq_sup_of_ray_ne_of_le hΦ hdim hpq hp hq, ← hpt', ← htt',
    ← cone_eq_sup_of_ray_ne_of_le hΨ hdim hne hpt htt]
  exact τ.property

/-- On a fixed rank-two lattice, complete regular fans with the same primitive ray generators
have the same cones. -/
theorem eq_of_range_primitiveGenerator_eq {Ψ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      Set.range (Ray.primitiveGenerator (Phi := Ψ))) : Φ = Ψ := by
  have hdim : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hsub {A B : Fan i} (hA : A.IsRegular) (hB : B.IsRegular)
      (hcA : A.IsComplete) (hcB : B.IsComplete)
      (h : Set.range (Ray.primitiveGenerator (Phi := A)) =
        Set.range (Ray.primitiveGenerator (Phi := B))) : A.cones ⊆ B.cones := by
    intro σ hσ
    obtain ⟨τ, hστ, hτ⟩ := exists_le_cone_of_card_toricRay_eq_two hA hcA hdim ⟨σ, hσ⟩
    exact B.mem_of_isFaceOf (mem_cones_of_range_primitiveGenerator_eq b hA hB hcB h hτ)
      (A.isFaceOf_of_le τ.property hσ hστ)
  exact Fan.ext (Set.Subset.antisymm (hsub hΦ hΨ hcΦ hcΨ hrays) (hsub hΨ hΦ hcΨ hcΦ hrays.symm))

end Fan

end TauCeti.Toric
