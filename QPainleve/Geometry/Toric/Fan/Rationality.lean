/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.Geometry.Toric.Fan.Adjacency
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import QPainleve.Geometry.Toric.Fan.FunctionField
import QPainleve.Geometry.Toric.Fan.Ray
import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Scheme
import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

/-!
# Rationality from an affine space chart

A fan containing the cone on an integral basis contains the standard affine space
fan as a subfan. The induced open immersion exhibits the toric variety as rational.
-/

public section

open AlgebraicGeometry CategoryTheory Module

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- A toric variety with a cone spanned by an integral basis is rational over
the complex base. -/
theorem isRationalOver_of_hull_basis_mem {ι : Type} [Finite ι]
    (b : Basis ι ℤ N) (h : PointedCone.hull ℝ (Set.range fun j ↦ i (b j)) ∈ Φ.cones) :
    Scheme.IsRationalOver (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
  let := Fintype.ofFinite ι
  let Ψ := affineSpace b Φ.lattice
  have hS : Ψ.cones ⊆ Φ.cones :=
    fun _ hσ ↦ Φ.mem_of_isFaceOf h ((mem_affineSpace_cones b Φ.lattice).mp hσ)
  let j := (Φ.subfanInclusion Ψ.cones hS Ψ.mem_of_isFaceOf).algebraicMap
  have he : Φ.subfan Ψ.cones hS Ψ.mem_of_isFaceOf = Ψ := by
    exact Fan.ext (Φ.subfan_cones Ψ.cones hS Ψ.mem_of_isFaceOf)
  let a := affineSpaceAlgebraicIso b Φ.lattice
  let g := a.inv ≫ (eqToIso (congrArg algebraicRealization he.symm)).hom ≫ j
  have : IsOpenImmersion g := inferInstanceAs
    (IsOpenImmersion (a.inv ≫ (eqToIso (congrArg algebraicRealization he.symm)).hom ≫ j))
  have : Nonempty Φ.cones := ⟨_, h⟩
  have : IsDominant g := inferInstance
  refine ⟨ι, (g.birationalOver _ _ ?_).symm⟩
  have hover {A B : Fan i} (hAB : A = B) :
      (eqToIso (congrArg algebraicRealization hAB)).hom.IsOver (Spec (CommRingCat.of ℂ)) := by
    subst B
    simp
  let := hover he.symm
  exact comp_over g (Spec (CommRingCat.of ℂ))

/-- A regular rank-two fan with two distinct rays in a common cone realizes
a rational surface. -/
theorem isRationalOver_of_ray_ne_of_le (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2)
    {ρ τ : Φ.Ray} {σ : Φ.cones} (hne : ρ ≠ τ) (hρ : ρ.toCone ≤ σ) (hτ : τ.toCone ≤ σ) :
    Scheme.IsRationalOver (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
  obtain ⟨b, hb₀, hb₁⟩ := Fan.exists_basis_of_ray_ne_of_le
    (Fan.isRegular_iff.mp hΦ _ σ.property) hN hne hρ hτ
  have hcone := Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN hne hρ hτ
  apply Φ.isRationalOver_of_hull_basis_mem b
  have hpair : Set.range (fun j : Fin 2 ↦ i (b j)) = {i (b 0)} ∪ {i (b 1)} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  rw [Ray.toCone_eq_hull_primitiveGenerator, Ray.toCone_eq_hull_primitiveGenerator,
    ← hb₀, ← hb₁, ← Submodule.span_union, ← hpair] at hcone
  have hσ : σ.val = PointedCone.hull ℝ (Set.range fun j : Fin 2 ↦ i (b j)) := hcone
  rw [← hσ]
  exact σ.property

/-- A complete regular rank-two fan realizes a rational surface. -/
theorem isRationalOver_of_isComplete (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (b : Basis (Fin 2) ℤ N) :
    Scheme.IsRationalOver (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) := by
  have : Nontrivial N := b.equivFun.toEquiv.nontrivial
  obtain ⟨ρ⟩ := Φ.nonempty_ray_of_isComplete hc
  obtain ⟨τ, ⟨hdet, σ, hr, ht⟩, -⟩ := (exists_unique_ray_neighbor_on_each_side b hΦ hc ρ).1
  have hne : ρ ≠ τ := by
    intro h
    rw [← h, b.detDualEquiv_self] at hdet
    exact zero_ne_one hdet
  exact Φ.isRationalOver_of_ray_ne_of_le hΦ
    ((finrank_eq_card_basis b).trans (Fintype.card_fin 2)) hne hr ht

end TauCeti.Toric.Fan
