/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Inversion
public import QPainleve.Geometry.Toric.Fan.Ruling.Basic

/-!
# Reversing a toric ruling character

Negating a ruling character swaps the two homogeneous coordinates on the
target projective line. The equality on affine toric charts identifies the
scheme morphisms, including along both invariant fibers.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (m : N →+ ℤ)

/-- The ruling for the negative character is the original ruling followed by the
homogeneous coordinate swap of the projective line. -/
theorem characterRuling_neg
    (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    (hneg : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (-m) x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter (-m) x ≤ 0) :
    Φ.characterRuling (-m) hneg =
      Φ.characterRuling m h ≫ (projectiveLine.coordinateSwap ℂ).hom := by
  apply Φ.algebraicRealization_hom_ext
  intro σ
  obtain ⟨k, hm⟩ : ∃ k : Fin 2, (if k = 0 then m else -m) ∈ dualSemigroup Φ.lattice σ.val := by
    rcases h σ with hp | hn
    · exact ⟨0, by simpa using (mem_dualSemigroup Φ.lattice m).2 hp⟩
    · exact ⟨1, by simpa using hn⟩
  have hk : (if k.rev = 0 then -m else - -m) = (if k = 0 then m else -m) := by
    fin_cases k <;> simp
  have hm' : (if k.rev = 0 then -m else - -m) ∈ dualSemigroup Φ.lattice σ.val := hk.symm ▸ hm
  rw [Φ.affineToricChartι_comp_characterRuling (-m) hneg σ k.rev hm', ← Category.assoc,
    Φ.affineToricChartι_comp_characterRuling m h σ k hm, Category.assoc,
    projectiveLine.polynomialChartι_comp_coordinateSwap]
  have hchars : (⟨_, hm'⟩ : dualSemigroup Φ.lattice σ.val) = ⟨_, hm⟩ := Subtype.ext hk
  rw [hchars]

end TauCeti.Toric.Fan
