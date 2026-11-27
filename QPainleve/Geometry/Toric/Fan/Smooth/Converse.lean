/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Fan.Basic

import QPainleve.Algebra.MonoidAlgebra.GradedCotangent
import QPainleve.Geometry.Toric.Cone.Regularity
import QPainleve.Geometry.Toric.BaseChange.FunctionField
import QPainleve.Geometry.Toric.RegularChart
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Recognizing regular surface fans from smoothness

At the vertex of the chart of a full-dimensional cone, each indecomposable
character contributes an independent cotangent direction. Smoothness limits their
number to the lattice rank. They generate the character lattice, so they are
a basis and its dual basis generates the original cone.

This is the affine toric smoothness criterion of Fulton, *Introduction to Toric
Varieties*, §2.1.
-/

public section

open AlgebraicGeometry CategoryTheory Module Submodule
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

universe u

variable (k : Type u) [Field k] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

namespace Fan

private theorem topologicalKrullDim_finiteFanScheme (Φ : Fan i) [Nonempty Φ.cones] :
    topologicalKrullDim (Φ.finiteFanScheme k) = finrank ℤ N := by
  let f := Φ.finiteFanSchemeToSpec k
  let hbot := Φ.bot_mem (inferInstance : Nonempty Φ.cones).some.property
  let j := Φ.affineChartι k ⟨⊥, hbot⟩
  have hdim : SmoothOfRelativeDimension (finrank ℤ N) (j ≫ f) := by
    change SmoothOfRelativeDimension _ (Φ.affineChartι k ⟨⊥, hbot⟩ ≫ Φ.finiteFanSchemeToSpec k)
    rw [Φ.affineChartι_finiteFanSchemeToSpec k ⟨⊥, hbot⟩]
    exact (isRegularCone_bot Φ.lattice).smoothOfRelativeDimension_affineChart (R := k) Φ.lattice
  rw [← topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType f j.isOpenEmbedding]
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (j ≫ f)

private theorem isRegularCone_of_smooth_of_span_eq_top (Φ : Fan i) (σ : Φ.cones)
    [Smooth (Φ.finiteFanSchemeToSpec k)] (hspan : span ℝ (σ.val : Set V) = ⊤) :
    IsRegularCone i σ.val := by
  let : Nonempty Φ.cones := ⟨σ⟩
  let hσ := Φ.isToricCone σ.property
  obtain ⟨d, hd⟩ := hσ.rational.exists_positive_degree_dualSemigroup Φ.lattice hspan
  let A := AddMonoidAlgebra k (dualSemigroup Φ.lattice σ.val)
  let P : Ideal A := (HomogeneousIdeal.irrelevant (AddMonoidAlgebra.gradeBy k d)).toIdeal
  let : P.IsMaximal := TauCeti.GradedAlgebra.isMaximal_toIdeal_irrelevant _
    (fun _ ↦ AddMonoidAlgebra.mem_bot_of_mem_gradeBy_zero d hd)
  let p : PrimeSpectrum A := ⟨P, inferInstance⟩
  let j := Φ.affineChartι k σ
  let f := Φ.finiteFanSchemeToSpec k
  have : Smooth (j ≫ f) := MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let : IsRegularLocalRing (Localization.AtPrime P) :=
    (isRegularLocalRing_stalk_Spec_iff (.of A) p).mp (isRegularLocalRing_stalk_of_smooth (j ≫ f) p)
  have hdim : ringKrullDim (Localization.AtPrime P) ≤ finrank ℤ N := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P]
    refine Ideal.height_le_ringKrullDim_of_isPrime.trans ?_
    have hj : topologicalKrullDim (PrimeSpectrum A) = topologicalKrullDim (Φ.finiteFanScheme k) :=
      topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType f j.isOpenEmbedding
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hj,
      Φ.topologicalKrullDim_finiteFanScheme k]
  obtain ⟨hfin, hcard⟩ :=
    AddMonoidAlgebra.finite_addIrreducible_and_card_le_of_isRegularLocalRing (k := k) d hd hdim
  exact hσ.isRegularCone_of_card_addIrreducible_le Φ.lattice d hd hcard

/-- A rank-two fan whose realization over a field is smooth has regular cones. -/
theorem isRegular_of_smooth_finiteFanSchemeToSpec (Φ : Fan i)
    (hN : finrank ℤ N = 2) [Smooth (Φ.finiteFanSchemeToSpec k)] : Φ.IsRegular := by
  apply isRegular_iff.mpr
  intro σ hσ
  let := Φ.lattice.finiteDimensional
  have hv : finrank ℝ V = 2 := Φ.lattice.finrank_eq.symm.trans hN
  by_cases hspan : span ℝ (σ : Set V) = ⊤
  · exact Φ.isRegularCone_of_smooth_of_span_eq_top k ⟨σ, hσ⟩ hspan
  · have hlt := Submodule.finrank_lt hspan
    exact (Φ.isToricCone hσ).isRegularCone_of_finrank_span_le_one Φ.lattice (by omega)

/-- For a rank-two fan, regularity is equivalent to smoothness of its realization over a field. -/
theorem isRegular_iff_smooth_finiteFanSchemeToSpec (Φ : Fan i)
    (hN : finrank ℤ N = 2) :
    Φ.IsRegular ↔ Smooth (Φ.finiteFanSchemeToSpec k) :=
  ⟨fun hΦ ↦
      have := Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec (R := k) hΦ
      SmoothOfRelativeDimension.smooth (finrank ℤ N) _,
    fun _ ↦ Φ.isRegular_of_smooth_finiteFanSchemeToSpec k hN⟩

end Fan

end TauCeti.Toric
