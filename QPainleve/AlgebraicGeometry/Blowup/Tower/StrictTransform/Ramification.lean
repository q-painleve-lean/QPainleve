/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.RegularCurve

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Ramification and strict transforms of regular curves

For a regular curve on a smooth surface, the exceptional part of its total
transform is bounded by the ramification divisor of the point blowup tower.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {C : X.IdealSheafData}
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]
  [PerfectField k] [IsNoetherian X]

local notation "f" => (X ↘ Spec (CommRingCat.of k))

/-- The total transform of a regular curve has multiplicity at most the ramification
multiplicity on every exceptional prime, after removing its strict transform. -/
theorem strictTransform_mul_ramification_le_totalTransform (hT : IsClosedPointTower X T)
    (hC : C.IsEffectiveCartier) (hdim : topologicalKrullDim C.subscheme = 1) :
    T.strictTransform C * hT.ramificationIdealSheafToBase k ≤ C.comap T.toBase := by
  classical
  induction hT with
  | nil => simp
  | @snoc d W U I hU p hp hI ih =>
    let g := U.toBase ≫ f
    have : IsIntegral W := hU.isIntegral f
    have : IsNoetherian W := U.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hU.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have := isRegularLocalRing_stalk_of_smooth g p
    have hdp := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have hUCart := hU.isEffectiveCartier_strictTransform f hC
    have hstep := hUCart.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdp
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    rw [← hcenter] at hstep
    have hE : I.comap I.blowupToBase ≤
        (I.comap I.blowupToBase) ^ ((U.strictTransform C).stalkOrder p).toNat := by
      by_cases h : p ∈ ((U.strictTransform C).support : Set W)
      · simp [hU.stalkOrder_strictTransform_eq_one_of_mem_support f hC hdim h]
      · simp [((U.strictTransform C).stalkOrder_eq_zero_iff p).mpr h]
    rw [strictTransform_snoc, ramificationIdealSheafToBase_snoc, ← mul_assoc, toBase_snoc,
      comap_comp]
    calc
      _ ≤ ((I.blowupMap (U.strictTransform C).subschemeι).ker *
          (I.comap I.blowupToBase) ^ ((U.strictTransform C).stalkOrder p).toNat) *
          (hU.ramificationIdealSheafToBase k).comap I.blowupToBase := by
        intro V
        simp only [ideal_mul, Pi.mul_apply]
        exact Ideal.mul_mono (Ideal.mul_mono le_rfl (hE V)) le_rfl
      _ ≤ _ := by
        rw [← hstep, ← comap_mul]
        exact comap_mono _ ih

end QPainleve.BlowupTower.IsClosedPointTower
