/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Degree.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

import QPainleve.AlgebraicGeometry.IdealSheaf.PointOrder
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Multiplicity and degree of a divisor on a curve

The degree of an effective Cartier divisor on a proper integral curve bounds its
vanishing order at a Cartier point, weighted by the degree of that point.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

/-- At a closed point with Cartier ideal, the degree of an effective Cartier divisor
on a proper integral curve bounds its order weighted by the residue degree. -/
theorem mul_residueDegree_le_eulerDegree_of_le_stalkOrder
    {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
    {D : C.IdealSheafData} (hD : D.IsEffectiveCartier) {p : C} (hp : IsClosed ({p} : Set C))
    (hP : (C.fromSpecResidueField p).ker.IsEffectiveCartier)
    {n : ℕ} (hn : (n : ℕ∞) ≤ D.stalkOrder p) :
    (n : ℤ) * ((C ↘ Spec (.of k)).residueDegree p : ℤ) ≤
      eulerDegree k (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
  let P := (C.fromSpecResidueField p).ker
  let F := D.colon (P ^ n)
  have hPn := isEffectiveCartier_pow hP n
  have hle := (natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField p D hp n).mp hn
  have hF : F.IsEffectiveCartier := hD.colon hPn.locallyPrincipal hle
  have hfactor := D.eq_colon_mul (P ^ n) hPn.locallyPrincipal hle
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have : IsFinite (F.subschemeι ≫ C ↘ Spec (.of k)) := hF.isFinite_subschemeι_comp
  have hpos : 0 ≤ eulerDegree k (LineBundleClass.mk hF.toInvertibleSheaf)⁻¹ := by
    rw [hF.eulerDegree_inv_mk_toInvertibleSheaf k F default]
    positivity
  rw [mk_toInvertibleSheaf_congr hD (isEffectiveCartier_mul hF hPn) hfactor,
    mk_toInvertibleSheaf_mul hF hPn, mk_toInvertibleSheaf_pow hP n, mul_inv_rev,
    eulerDegree_mul_of_isIntegral, ← inv_pow, ← zpow_natCast,
    eulerDegree_zpow_of_isCurveOver, eulerDegree_inv_of_isIntegral,
    eulerDegree_mk_ker_fromSpecResidueField hp hP, neg_neg]
  omega

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
