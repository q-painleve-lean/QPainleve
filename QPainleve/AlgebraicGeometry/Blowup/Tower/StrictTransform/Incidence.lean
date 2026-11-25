/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Fin.Embedding
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

universe u v

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

/-- If the new strict-transform coefficients prepend zeros to reindexed old
coefficients, the incident centers are exactly the corresponding tail indices. -/
theorem strictTransformCenterIndices_eq_map_of_coefficients_eq_append_zero
    {X' Y' : Scheme.{v}} {m k : ℕ} {U : BlowupTower X' (k + m) Y'}
    {C' : X'.IdealSheafData} (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U)
    (f : Fin m → Fin n) (h : hU.strictTransformCoefficients C' =
      Fin.append (0 : Fin k → ℤ) (hT.strictTransformCoefficients C ∘ f)) :
    hU.strictTransformCenterIndices C' =
      (Finset.univ.filter fun l ↦ f l ∈ hT.strictTransformCenterIndices C).map
        (Fin.natAddEmb k) := by
  ext l
  refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) l
  · simp only [mem_strictTransformCenterIndices, h, Fin.append_left, Pi.zero_apply,
      ne_self_iff_false, false_iff, Finset.mem_map, not_exists, not_and]
    intro b _ hab
    have he := congrArg Fin.val hab
    simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.val_castAdd] at he
    omega
  · rw [← Fin.natAddEmb_apply, Finset.mem_map']
    simp only [Fin.natAddEmb_apply, mem_strictTransformCenterIndices, h, Fin.append_right,
      Function.comp_apply, Finset.mem_filter, Finset.mem_univ, true_and]

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
