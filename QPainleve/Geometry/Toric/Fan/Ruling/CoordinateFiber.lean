/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Torus

import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse

/-!
# Coordinate fibers of a character ruling

The two invariant points of the projective line lie off its dense torus.
Negating a toric ruling character exchanges the two scheme-theoretic
coordinate fibers.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open Scheme.IdealSheafData TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric

local notation "coordPoint[" j "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0

/-- A polynomial point with affine coordinate zero lies outside the dense torus. -/
theorem polynomialPoint_zero_notMem_range_projectiveLineTorusι (j : Fin 2)
    (x : Spec (CommRingCat.of ℂ)) :
    coordPoint[j] x ∉ Set.range projectiveLineTorusι := by
  have hother : coordPoint[j] x ∉ Set.range (projectiveLine.polynomialChartι ℂ j.rev) := by
    rw [projectiveLine.polynomialPoint_def, Scheme.Hom.comp_apply,
      projectiveLine.polynomialChartι_mem_range_iff]
    rw [not_not, Spec.map_apply]
    exact Ideal.mem_comap.mpr (by
      simp [Polynomial.eval₂RingHom])
  rw [range_projectiveLineTorusι]
  fin_cases j
  · exact fun h ↦ hother h.2
  · exact fun h ↦ hother h.1

namespace Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) [Nonempty Φ.cones] (m : N →+ ℤ)
  (h : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter m x ≤ 0)
  (hneg : ∀ σ : Φ.cones, (∀ x ∈ σ.val, 0 ≤ Φ.lattice.realCharacter (-m) x) ∨
    ∀ x ∈ σ.val, Φ.lattice.realCharacter (-m) x ≤ 0)

/-- Negating the ruling character interchanges the two scheme-theoretic coordinate fibers. -/
theorem comap_ker_coordinatePoint_characterRuling_neg (hm : m ≠ 0) (hΦ : Φ.IsRegular)
    (j : Fin 2) :
    (coordPoint[j]).ker.comap (Φ.characterRuling (-m) hneg) =
      (coordPoint[j.rev]).ker.comap (Φ.characterRuling m h) := by
  have hover (k : Fin 2) : coordPoint[k] ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _ := by
    simp [projectiveLine.polynomialPoint_over]
  have hne : -m ≠ 0 := neg_ne_zero.mpr hm
  let h₁ := Φ.isEffectiveCartier_characterRuling_fiber (-m) hneg hne coordPoint[j] (hover j)
  let h₂ := Φ.isEffectiveCartier_characterRuling_fiber m h hm coordPoint[j.rev] (hover j.rev)
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  apply (h₁.toCartierDivisor_eq_iff h₂).mp
  apply toWeilDivisor_injective
  rw [Φ.toWeilDivisor_characterRuling_coordinateFiber (-m) hneg hne j hΦ,
    Φ.toWeilDivisor_characterRuling_coordinateFiber m h hm j.rev hΦ]
  fin_cases j <;> simp

end Fan

end TauCeti.Toric
