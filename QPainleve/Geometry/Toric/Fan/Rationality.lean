/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import QPainleve.Geometry.Toric.Fan.FunctionField
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

end TauCeti.Toric.Fan
