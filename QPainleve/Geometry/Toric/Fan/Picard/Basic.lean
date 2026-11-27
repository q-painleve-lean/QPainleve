/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Affine.Picard
public import QPainleve.Geometry.Toric.BaseChange.Fan

import QPainleve.Geometry.Toric.RegularChart

/-!
# Trivial Picard group of a regular toric chart

The coordinate ring of a regular cone chart over a factorial domain is factorial.
In particular the dense torus, given by the zero cone, has trivial Picard group.
This is used in Picard excision along the dense-torus inclusion.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

open TauCeti.AlgebraicGeometry (LineBundleClass)

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- A regular affine toric chart over a factorial domain has trivial Picard group. -/
theorem IsRegularCone.subsingleton_lineBundleClass_affineChart
    (hσ : IsRegularCone i σ) (hi : IsIntegralLattice i)
    (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (LineBundleClass (Spec (.of (affineChartRing R hi σ)))) := by
  have := hσ.uniqueFactorizationMonoid_affineChartRing R hi
  have : IsDomain (affineChartRing R hi σ) := NoZeroDivisors.to_isDomain _
  exact LineBundleClass.subsingleton_spec (affineChartRing R hi σ)

end TauCeti.Toric
