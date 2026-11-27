/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Point
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic

/-!
# Distinguished points of character rulings

A distinguished point of a cone maps to the origin of the corresponding ruling
chart whenever the ruling character is nonzero on the cone. In a toric
Hirzebruch link this identifies the ruling fibers of the source and reverse
centers, using the same character on both fans.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

variable (K : Type) [CommRing K] {N : Type} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

/-- In the projective chart determined by the sign of the character, the image of a
distinguished point has coordinate zero when the character is nonzero on its cone. -/
theorem distinguishedPointHom_comp_characterRuling
    (m : N →+ ℤ)
    (h : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ γ.val, Φ.lattice.realCharacter m x ≤ 0)
    (σ : Φ.cones) (k : Fin 2)
    (hm : (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val)
    (hσ : ∃ x ∈ σ.val, Φ.lattice.realCharacter m x ≠ 0) :
    Φ.distinguishedSection (R := K) σ ≫ Φ.characterRuling K m h =
      projectiveLine.polynomialPoint K (RingHom.id K) k 0 := by
  classical
  let a : dualSemigroup Φ.lattice σ.val := ⟨_, hm⟩
  let d := facePointAlgebraHom Φ.lattice (⊤ : σ.val.Face) K
  have hd : d (AddMonoidAlgebra.single a 1) = 0 := by
    obtain ⟨x, hx, hx₀⟩ := hσ
    rw [facePointAlgebraHom_single, ite_eq_right]
    intro hz
    have hz₀ := hz x hx
    by_cases hk : k = 0 <;> simp [a, hk, hx₀] at hz₀
  have hev : d.comp (Polynomial.aeval (AddMonoidAlgebra.single a 1)) =
      Polynomial.aeval 0 := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply, Polynomial.aeval_X] using hd
  rw [distinguishedSection_def, Category.assoc,
    Φ.affineToricChartι_comp_characterRuling K m h σ k hm, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, projectiveLine.polynomialPoint_def]
  exact congrArg (fun f : Polynomial K →+* K ↦
    Spec.map (CommRingCat.ofHom f) ≫ projectiveLine.polynomialChartι K k)
    (congrArg AlgHom.toRingHom hev)

/-- The source corner and the reverse corner of a toric Hirzebruch link have the
same image under the common ruling. -/
theorem characterRuling_distinguishedPointHom_eq_of_hirzebruch_link
    (b d : Basis (Fin 2) ℤ N) (hd₀ : d 0 = b 0) (hd₁ : d 1 = b 0 + b 1)
    (σ : Φ.cones) (τ : Ψ.cones)
    (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
    (hτ : τ.val = hull ℝ {i (d 1), i (-d 0)})
    (h₀ : ∀ γ : Φ.cones, (∀ x ∈ γ.val, 0 ≤ Φ.lattice.realCharacter
      (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
        Φ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0)
    (h₁ : ∀ γ : Ψ.cones, (∀ x ∈ γ.val, 0 ≤ Ψ.lattice.realCharacter
      (b.coord 1).toAddMonoidHom x) ∨ ∀ x ∈ γ.val,
        Ψ.lattice.realCharacter (b.coord 1).toAddMonoidHom x ≤ 0) (x : Spec (.of K)) :
    Φ.characterRuling K (b.coord 1).toAddMonoidHom h₀ (Φ.distinguishedSection (R := K) σ x) =
      Ψ.characterRuling K (b.coord 1).toAddMonoidHom h₁ (Ψ.distinguishedSection (R := K) τ x) := by
  let m := (b.coord 1).toAddMonoidHom
  have hs : m ∈ dualSemigroup Φ.lattice σ.val := by
    rw [hσ, Set.range_comp, mem_dualSemigroup_hull_image, Set.forall_mem_range]
    intro j
    fin_cases j <;> simp [m]
  have ht : m ∈ dualSemigroup Ψ.lattice τ.val := by
    rw [hτ, ← Set.image_pair, mem_dualSemigroup_hull_image]
    simp [m, hd₀, hd₁]
  have hsrc : ∃ x ∈ σ.val, Φ.lattice.realCharacter m x ≠ 0 := by
    refine ⟨i (b 1), hσ ▸ subset_hull (Set.mem_range_self (1 : Fin 2)), ?_⟩
    simp [m, IsIntegralLattice.realCharacter_apply]
  have htgt : ∃ x ∈ τ.val, Ψ.lattice.realCharacter m x ≠ 0 := by
    refine ⟨i (d 1), hτ ▸ subset_hull (Set.mem_insert _ _), ?_⟩
    simp [m, hd₁, IsIntegralLattice.realCharacter_apply]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    Φ.distinguishedPointHom_comp_characterRuling K m h₀ σ 0 (by simpa using hs) hsrc,
    Ψ.distinguishedPointHom_comp_characterRuling K m h₁ τ 0 (by simpa using ht) htgt]

end TauCeti.Toric.Fan
