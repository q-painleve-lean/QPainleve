/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection

import QPainleve.AlgebraicGeometry.Cohomology.ProjectiveSpace.EulerCharacteristic

/-!
# The intersection form of the projective plane

The Euler characteristic of a line bundle on the projective plane is the quadratic
polynomial in its Picard coordinate given by the cohomology of the twists. Its mixed
difference identifies the native surface intersection pairing with integer multiplication.
In particular, the hyperplane generator has square one. The calculation combines
`QPainleve.eulerCharBelow_twistingSheaf_projectivePlane` with Tau Ceti's
`Chow.classIntersectionNumber_eq`.
-/

public section

open AlgebraicGeometry
open TauCeti.SymmetricAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k]

local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k (Fin 3))

/-- The Euler characteristic of a projective-plane class is `(d+1)(d+2)/2`, where
`d` is its coordinate in the Picard group. -/
theorem LineBundleClass.eulerCharBelow_projectivePlane (a : LineBundleClass P) :
    eulerCharBelow k a 3 =
      (degree (Additive.ofMul a) + 1) * (degree (Additive.ofMul a) + 2) / 2 := by
  let d := degree (Additive.ofMul a)
  have ha : mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) d) = a :=
    ((Pi.basisFun k (Fin 3)).picardTwistEquiv_symm_apply d).symm.trans
      (congrArg Additive.toMul (AddEquiv.symm_apply_apply degree (Additive.ofMul a)))
  calc
    eulerCharBelow k a 3 = eulerCharBelow k (mk (Proj.symmetricAlgebraTwistingBundle
        k (Fin 3 → k) d)) 3 := congrArg (fun c ↦ eulerCharBelow k c 3) ha.symm
    _ = (d + 1) * (d + 2) / 2 := by
      rw [eulerCharBelow_mk, Proj.symmetricAlgebraTwistingBundle_obj]
      exact QPainleve.eulerCharBelow_twistingSheaf_projectivePlane k d

private theorem projectivePlane_mixed_difference (a b : ℤ) :
    1 - ((-a + 1) * (-a + 2)) / 2 - ((-b + 1) * (-b + 2)) / 2 +
      ((-a + -b + 1) * (-a + -b + 2)) / 2 = a * b := by
  have h (m : ℤ) : (m + 1) * (m + 2) / 2 * 2 = (m + 1) * (m + 2) := by
    have he : m + 1 + 1 = m + 2 := by omega
    exact Int.ediv_mul_cancel (by simpa only [he] using Int.two_dvd_mul_add_one (m + 1))
  nlinarith only [h (-a), h (-b), h (-a + -b)]

/-- In the hyperplane basis, the intersection pairing of the projective plane is
multiplication of the two integral Picard coordinates. -/
theorem Chow.classIntersectionNumber_projectivePlane (a b : LineBundleClass P) :
    classIntersectionNumber k P a b =
      degree (Additive.ofMul a) * degree (Additive.ofMul b) := by
  rw [classIntersectionNumber_eq]
  simp only [LineBundleClass.eulerCharBelow_projectivePlane, ofMul_one,
    ofMul_inv, ofMul_mul, map_zero, map_neg, map_add]
  norm_num
  exact projectivePlane_mixed_difference _ _

end TauCeti.AlgebraicGeometry
