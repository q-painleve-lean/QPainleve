/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import QPainleve.Geometry.Toric.RegularChart

/-!
# Smoothness of regular toric fan schemes

A fan whose cones are regular has smooth algebraic realization over `ℂ`, of relative dimension
the rank of its lattice. Smoothness is checked on Tau Ceti's `Fan.affineToricOpenCover`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The affine scheme of a regular cone is smooth over `ℂ`, of relative dimension
the lattice rank. -/
theorem IsRegularCone.smoothOfRelativeDimension_affineToricScheme
    {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i) :
    SmoothOfRelativeDimension (Module.finrank ℤ N)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) :
        affineToricScheme hi σ ⟶ Spec (.of ℂ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Module.finrank ℤ N))
    (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension (Module.finrank ℤ N))),
    CommRingCat.hom_ofHom]
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (n := Module.finrank ℤ N))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact hσ.isStandardSmoothOfRelativeDimension_affineCoordinateRing hi

namespace Fan

/-- The realization of a regular fan is smooth over `ℂ` of relative dimension the lattice rank. -/
theorem smoothOfRelativeDimension_algebraicRealizationStructureMap (Φ : Fan i) (hΦ : Φ.IsRegular) :
    SmoothOfRelativeDimension (Module.finrank ℤ N) Φ.algebraicRealizationStructureMap := by
  let n := Module.finrank ℤ N
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension n))
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @SmoothOfRelativeDimension n) Φ.affineToricOpenCover).2
  intro σ
  -- The cone index of this chart is hidden behind the open cover's bundled index type.
  let cone : Φ.cones := σ
  suffices SmoothOfRelativeDimension n
    (Φ.affineToricChartι cone ≫ Φ.algebraicRealizationStructureMap) from this
  rw [Φ.affineToricChartι_comp_algebraicRealizationStructureMap cone]
  exact (isRegular_iff.mp hΦ cone.val cone.property).smoothOfRelativeDimension_affineToricScheme
    Φ.lattice

/-- The structure morphism of a regular toric fan scheme is smooth. -/
theorem smooth_algebraicRealizationStructureMap (Φ : Fan i) (hΦ : Φ.IsRegular) :
    Smooth Φ.algebraicRealizationStructureMap :=
  have := Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  SmoothOfRelativeDimension.smooth (Module.finrank ℤ N) _

end Fan

end TauCeti.Toric
