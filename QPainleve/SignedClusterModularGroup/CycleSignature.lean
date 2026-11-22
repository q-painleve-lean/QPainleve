/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.BoundaryCycle
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Boundary cycle length and signature

A boundary cycle with nonzero total class has length strictly below the rank of a
nondegenerate integral lattice. Tau Ceti's orthogonal signature decomposition expresses
the rank as the sum of the positive and negative indices, giving the nine-component bound
in signature `(1, 9)`.
-/

public section

open LinearMap

namespace QPainleve.BoundaryCycle

variable {n : ℕ} [NeZero n] {L : Type*} [AddCommGroup L]
  [Module.Free ℤ L] [Module.Finite ℤ L]
  {B : LinearMap.BilinForm ℤ L} {D : ZMod n → L}
  (hGram : ∀ i j, B (D i) (D j) =
    (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
  (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

include hGram

/-- For a nondegenerate symmetric integral form, the length of a boundary cycle with
nonzero total class is strictly less than the sum of the positive and negative indices. -/
theorem length_lt_sigPos_add_sigNeg (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hδ : ∑ i, D i ≠ 0) :
    n < sigPos (B.baseChange K).toQuadraticMap + sigNeg (B.baseChange K).toQuadraticMap := by
  have hndK := (B.nondegenerate_baseChange_iff (A := K) (Module.Free.chooseBasis ℤ L)).mpr hnd
  have hsymmK := BilinForm.IsSymm.baseChange K (BilinForm.isSymm_iff.mp hB)
  have hreg := hndK.toQuadraticMap (LinearMap.ext₂ fun x y ↦ hsymmK.eq y x)
  rw [QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _ hreg, Module.finrank_baseChange]
  exact length_lt_finrank hGram hnd hδ

/-- A boundary cycle with nonzero total class in a nondegenerate integral lattice of
signature `(1, 9)` has at most nine components. -/
theorem length_le_nine_of_signature_one_nine (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hδ : ∑ i, D i ≠ 0)
    (hpos : sigPos (B.baseChange K).toQuadraticMap = 1)
    (hneg : sigNeg (B.baseChange K).toQuadraticMap = 9) : n ≤ 9 := by
  have h := length_lt_sigPos_add_sigNeg hGram K hB hnd hδ
  omega

end QPainleve.BoundaryCycle
