/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Affine.Picard
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus

import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import QPainleve.Geometry.Toric.RegularChart
import TauCeti.Geometry.Toric.Algebraic.Normal

/-!
# Factorial toric charts and the Picard group of the dense torus

The coordinate ring of a regular cone chart is factorial by
`IsRegularCone.uniqueFactorizationMonoid_affineCoordinateRing`, and so are its localizations.
The dense torus is the chart of the zero cone, so
`LineBundleClass.subsingleton_spec` gives the vanishing of its Picard group. These are
inputs to Picard excision along the dense-torus inclusion.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric

open TauCeti.AlgebraicGeometry (LineBundleClass)

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- Every line bundle on a regular affine cone chart is trivial. -/
theorem IsRegularCone.subsingleton_lineBundleClass_affineToricScheme (hσ : IsRegularCone i σ)
    (hi : IsIntegralLattice i) : Subsingleton (LineBundleClass (affineToricScheme hi σ)) := by
  have := hσ.uniqueFactorizationMonoid_affineCoordinateRing hi
  exact LineBundleClass.subsingleton_spec (affineCoordinateRing hi σ)

/-- Every line bundle on the dense torus of an integral lattice is trivial. -/
instance subsingleton_lineBundleClass_denseTorusScheme (hi : IsIntegralLattice i) :
    Subsingleton (LineBundleClass (denseTorusScheme hi)) :=
  (isRegularCone_bot hi).subsingleton_lineBundleClass_affineToricScheme hi

namespace Fan

/-- The stalk at any point of a regular toric fan is factorial. -/
theorem uniqueFactorizationMonoid_stalk_algebraicRealization (Φ : Fan i) (hΦ : Φ.IsRegular)
    (x : Φ.algebraicRealization) :
    UniqueFactorizationMonoid (Φ.algebraicRealization.presheaf.stalk x) := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  let R := CommRingCat.of (affineCoordinateRing Φ.lattice σ.val)
  have : UniqueFactorizationMonoid R :=
    (isRegular_iff.1 hΦ σ.val σ.property).uniqueFactorizationMonoid_affineCoordinateRing Φ.lattice
  have : y.asIdeal.IsPrime := y.isPrime
  let : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hstalk := UniqueFactorizationMonoid.of_isLocalization y.asIdeal.primeCompl
    ((Spec R).presheaf.stalk y)
  exact (asIso ((Φ.affineToricChartι σ).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid hstalk

end Fan

end TauCeti.Toric
