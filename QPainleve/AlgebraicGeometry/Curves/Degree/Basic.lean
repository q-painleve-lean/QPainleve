/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Degree

import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Euler degrees of tensor powers on proper integral curves

Additivity of the Euler degree under tensor product gives the degree formula for
integer tensor powers, including on singular integral curves.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {X : Scheme.{u}} (k : Type u) [Field k]
  [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- The Euler degree of an integer tensor power on a proper integral curve. -/
@[simp]
theorem eulerDegree_zpow_of_isCurveOver (a : LineBundleClass X) (n : ℤ) :
    eulerDegree k (a ^ n) = n * eulerDegree k a := by
  have : RelativeDimensionLE 1 (X ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  let deg : Additive (LineBundleClass X) →+ ℤ :=
    AddMonoidHom.mk' (fun c ↦ eulerDegree k c.toMul) fun b c ↦
      eulerDegree_mul_of_isIntegral k b.toMul c.toMul
  simpa [deg, zsmul_eq_mul] using deg.map_zsmul n (Additive.ofMul a)

end TauCeti.AlgebraicGeometry.LineBundleClass
