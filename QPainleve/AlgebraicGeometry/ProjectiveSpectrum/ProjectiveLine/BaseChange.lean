/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

/-!
# Composition of projective-line base changes

The native coefficient extensions of the projective line compose along a tower
of algebras. This identifies successive chart restrictions with a single
restriction on the coefficients.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Successive coefficient extensions induce the projection for the composite extension. -/
@[reassoc (attr := simp)]
theorem baseChangeProjection_comp_baseChangeProjection :
    baseChangeProjection A B ≫ baseChangeProjection R A = baseChangeProjection R B := by
  rw [baseChangeProjection_eq_map A B, baseChangeProjection_eq_map R A,
    baseChangeProjection_eq_map R B, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.toRingHom_injective
  apply _root_.SymmetricAlgebra.ringHom_ext
  · ext r
    simp [GradedRingHom.coe_toRingHom, ← IsScalarTower.algebraMap_apply R A B]
  · intro m
    simp [GradedRingHom.coe_toRingHom, ← IsScalarTower.algebraMap_apply R A B]

end TauCeti.AlgebraicGeometry.projectiveLine
