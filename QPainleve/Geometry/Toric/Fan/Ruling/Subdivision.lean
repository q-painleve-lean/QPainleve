/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

/-!
# Character rulings on common subdivisions

The character ruling to the projective line is compatible with passage between
fans in a fixed lattice, including the two projections of a toric elementary link.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan.IsSubdivision

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Ω Φ Ψ : Fan i}

/-- The two pullbacks of a shared character ruling to a common subdivision agree. -/
theorem comp_characterRuling_eq (s : Ω.IsSubdivision Φ) (t : Ω.IsSubdivision Ψ)
    (m : N →+ ℤ)
    (hΦ : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
    (hΨ : ∀ σ : Ψ.cones, (∀ x ∈ σ.val, 0 ≤ Ψ.lattice.realCharacter m x) ∨
      ∀ x ∈ σ.val, Ψ.lattice.realCharacter m x ≤ 0) :
    s.toFanHom.algebraicMap ≫ Φ.characterRuling m hΦ =
      t.toFanHom.algebraicMap ≫ Ψ.characterRuling m hΨ := by
  have h : (Φ.characterFanHom m hΦ).comp s.toFanHom =
      (Ψ.characterFanHom m hΨ).comp t.toFanHom := by
    apply FanHom.ext
    ext x j
    simp [FanHom.comp_latticeMap]
  simp only [characterRuling_def, ← Category.assoc, ← FanHom.algebraicMap_comp, h]

end TauCeti.Toric.Fan.IsSubdivision
