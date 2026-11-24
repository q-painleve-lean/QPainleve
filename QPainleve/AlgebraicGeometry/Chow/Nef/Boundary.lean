/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Support

/-!
# Nef square-zero divisors and the boundary orthogonal

The class of a nef effective Cartier divisor has square zero precisely when it is
orthogonal to all the prime curves in its support.
-/

public section

open AlgebraicGeometry TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)

/-- For a nef effective Cartier divisor, membership of its class in the boundary orthogonal
is equivalent to vanishing self-intersection. -/
theorem effectiveCartierClass_mem_boundaryOrthogonal_iff_of_isNef
    (hnef : (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹.IsNef k (X ↘ Spec (.of k))) :
    Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ ∈ D.boundaryOrthogonal k ↔
      Chow.classIntersectionNumber k X (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = 0 := by
  let f := X ↘ Spec (.of k)
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let := f.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let W := hD.toCartierDivisor.toWeilDivisor
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hD.isEffective_toCartierDivisor
  have hclass : (Scheme.CartierDivisor.weilToLineBundleClassHom X W).toMul =
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
    rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul,
      hD.toLineBundleClass_toCartierDivisor]
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have h := Chow.classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff
    k hdim hW (hclass.symm ▸ hnef)
  rw [hclass] at h
  let U : X.Opens := D.support.compl
  have hs (p : CodimensionOnePoint X) : p ∈ W.support ↔ (p : X) ∉ U := by
    calc
      p ∈ W.support ↔ W p ≠ 0 := Finsupp.mem_support_iff
      _ ↔ (p : X) ∈ D.support := by
        simpa only [W, WeilDivisor.coeff, not_not] using
          not_congr (hD.coeff_toWeilDivisor_eq_zero_iff p)
      _ ↔ (p : X) ∉ U := not_not.symm
  have hspan := U.primeDivisorSpanCompl_eq_span_of_mem_iff
    (Subtype.val : W.support → CodimensionOnePoint X) fun p ↦ by
      simpa only [Subtype.range_val_subtype, Set.mem_ofPred_eq, Finset.mem_coe] using (hs p).symm
  rw [h, D.boundaryOrthogonal_def k, hspan, LinearMap.BilinForm.orthogonal,
    Submodule.mem_orthogonalBilin_span]
  simp only [Set.forall_mem_range, Subtype.forall, Chow.intersectionBilinForm_apply,
    toMul_ofMul,
    Chow.classIntersectionNumber_comm (b := (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹)]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
