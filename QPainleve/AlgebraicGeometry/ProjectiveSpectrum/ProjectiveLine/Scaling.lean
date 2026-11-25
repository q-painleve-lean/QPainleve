/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Base change of projective-line coordinates

Unit scaling in a homogeneous coordinate commutes with changing the coefficient
ring. This lets one compare projective bundle transitions written in different
coordinates on the base.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Base change takes a projective scaling to scaling by the image of its unit. -/
@[reassoc]
theorem baseChangeProjection_comp_scalingBy (v : Aˣ) :
    baseChangeProjection A B ≫ (scalingBy A v).hom =
      (scalingBy B (v.map (algebraMap A B))).hom ≫ baseChangeProjection A B := by
  have : IsSeparated (terminal.from (projectiveLine A)) := by
    rw [← terminal.comp_from (projectiveLine A ↘ Spec (.of A))]
    infer_instance
  refine TauCeti.ext_of_isSchemeTheoreticallyDominant (polynomialChartι B 1)
    (terminal.from _) (terminal.hom_ext _ _) ?_
  rw [← polynomialPoint_X]
  simp only [← Category.assoc, polynomialPoint_comp_baseChangeProjection,
    polynomialPoint_comp_scalingBy, Units.coe_map, RingHom.comp_apply,
    MonoidHom.coe_ofClass]

variable (C : Type u) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- In a tower of coefficient rings the projective-line base-change projections compose. -/
@[reassoc]
theorem baseChangeProjection_comp :
    baseChangeProjection B C ≫ baseChangeProjection A B = baseChangeProjection A C := by
  have : IsSeparated (terminal.from (projectiveLine A)) := by
    rw [← terminal.comp_from (projectiveLine A ↘ Spec (.of A))]
    infer_instance
  refine TauCeti.ext_of_isSchemeTheoreticallyDominant (polynomialChartι C 1)
    (terminal.from _) (terminal.hom_ext _ _) ?_
  rw [← polynomialPoint_X]
  simp only [← Category.assoc, polynomialPoint_comp_baseChangeProjection,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A B C]

end TauCeti.AlgebraicGeometry.projectiveLine
