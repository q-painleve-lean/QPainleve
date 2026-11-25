/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Monotonicity of nef intersection on effective Cartier divisors

The residual divisor in an inclusion of effective Cartier divisors has
nonnegative intersection with a nef class.
-/

public section

open AlgebraicGeometry TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace TauCeti.AlgebraicGeometry.Chow

/-- Intersection with a nef class is monotone in the effective Cartier divisor.
The defining ideals are ordered by reverse inclusion. -/
theorem classIntersectionNumber_le_of_isNef_of_le_ideal
    (k : Type u) [Field k] [Infinite k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hX : topologicalKrullDim X = 2) {a : LineBundleClass X}
    (ha : a.IsNef k (X ↘ Spec (.of k))) {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) (hle : I ≤ J) :
    classIntersectionNumber k X a (mk hJ.toInvertibleSheaf)⁻¹ ≤
      classIntersectionNumber k X a (mk hI.toInvertibleSheaf)⁻¹ := by
  let hR := hI.colon hJ.locallyPrincipal hle
  have hclass := mk_toInvertibleSheaf_congr hI (TauCeti.isEffectiveCartier_mul hR hJ)
    (I.eq_colon_mul J hJ.locallyPrincipal hle)
  rw [hclass.trans (mk_toInvertibleSheaf_mul hR hJ), mul_inv_rev,
    classIntersectionNumber_mul_right k hX]
  exact le_add_of_nonneg_right (classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier
    k hX ha hR)

end TauCeti.AlgebraicGeometry.Chow
