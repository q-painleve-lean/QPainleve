/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
public import QPainleve.Geometry.Toric.Fan.Rationality

/-!
# Rationality of Hirzebruch surfaces

A section ray and an adjacent fiber ray give an affine plane chart on the
Hirzebruch surface. Its dense inclusion exhibits the surface as rational.
-/

public section

open AlgebraicGeometry CategoryTheory Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The algebraic realization of a complete regular Hirzebruch fan is rational over `ℂ`. -/
theorem isRationalOver_of_hirzebruch
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
    (hc : Φ.IsComplete) :
    Scheme.IsRationalOver (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
  obtain ⟨σ, h₀, h₁⟩ := exists_cone_of_hirzebruch_section_fiber b e r hr hΦ hc 0 0
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hcone := Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN
    (r.injective.ne (by decide : (0 : Fin 4) ≠ 1)) h₀ h₁
  have h₀' : (r 0).primitiveGenerator = b 0 := congrFun hr 0
  have h₁' : (r 1).primitiveGenerator = b 1 := congrFun hr 1
  rw [Ray.toCone_eq_hull_primitiveGenerator, Ray.toCone_eq_hull_primitiveGenerator,
    h₀', h₁', ← Submodule.span_union] at hcone
  apply Φ.isRationalOver_of_hull_basis_mem b
  have hpair : Set.range (fun j : Fin 2 ↦ i (b j)) = {i (b 0)} ∪ {i (b 1)} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  have hcone' : σ.val = PointedCone.hull ℝ ({i (b 0)} ∪ {i (b 1)}) := hcone
  rw [hpair, ← hcone']
  exact σ.property

end TauCeti.Toric.Fan
