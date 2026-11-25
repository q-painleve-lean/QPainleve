/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.RegularCurve

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk

/-!
# Centers on a regular curve in a point-blowup tower

The indices of centers lying on the current strict transform give the
exceptional coordinates of a regular curve. Incidence is measured on the
surface immediately before each blowup.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  {C : X.IdealSheafData}

open Classical in
/-- Indices with nonzero exceptional coordinates in the strict-transform class.
For a regular curve these are exactly the centers on the successive strict transforms. -/
def strictTransformCenterIndices (hT : IsClosedPointTower X T) (C : X.IdealSheafData) :
    Finset (Fin n) :=
  Finset.univ.filter fun j ↦ hT.strictTransformCoefficients C j ≠ 0

@[simp]
theorem mem_strictTransformCenterIndices (hT : IsClosedPointTower X T)
    (C : X.IdealSheafData) (j : Fin n) :
    j ∈ hT.strictTransformCenterIndices C ↔ hT.strictTransformCoefficients C j ≠ 0 := by
  classical
  simp [strictTransformCenterIndices]

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1)

include f hC hdim in
private theorem stalkOrder_strictTransform_eq_ite (hT : IsClosedPointTower X T)
    (p : Y) [Decidable (p ∈ (T.strictTransform C).support)] :
    (T.strictTransform C).stalkOrder p = if p ∈ (T.strictTransform C).support then 1 else 0 := by
  split_ifs with hp
  · exact hT.stalkOrder_strictTransform_eq_one_of_mem_support f hC hdim hp
  · exact ((T.strictTransform C).stalkOrder_eq_zero_iff p).mpr hp

include f hC hdim in
/-- The final index is selected precisely when the final center lies on the
strict transform made by the prefix tower. -/
theorem last_mem_strictTransformCenterIndices {I : Y.IdealSheafData}
    (h : IsClosedPointTower X (T.snoc I)) (p : Y) (hp : IsClosed ({p} : Set Y))
    (hI : I = (Y.fromSpecResidueField p).ker) :
    Fin.last n ∈ h.strictTransformCenterIndices C ↔ p ∈ (T.strictTransform C).support := by
  classical
  rw [mem_strictTransformCenterIndices, strictTransformCoefficients_snoc_last _ h p hp hI,
    stalkOrder_strictTransform_eq_ite f hC hdim (snoc_iff.mp h).1]
  split <;> simp [*]

include f hC hdim in
/-- For a regular curve the exceptional coordinate is minus one at each
incident center and zero elsewhere. -/
theorem strictTransformCoefficients_eq_ite (hT : IsClosedPointTower X T) (j : Fin n) :
    hT.strictTransformCoefficients C j =
      if j ∈ hT.strictTransformCenterIndices C then -1 else 0 := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d W U I hU p hp hI ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · classical
      simp only [last_mem_strictTransformCenterIndices f hC hdim _ p hp hI,
        strictTransformCoefficients_snoc_last _ _ p hp hI,
        stalkOrder_strictTransform_eq_ite f hC hdim hU]
      split <;> simp
    · simpa only [strictTransformCoefficients_snoc_castSucc,
        mem_strictTransformCenterIndices] using ih j

end QPainleve.BlowupTower.IsClosedPointTower
