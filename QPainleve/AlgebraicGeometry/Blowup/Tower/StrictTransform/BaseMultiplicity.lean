/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.MovingBaseIdeal
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic

import Mathlib.Data.Finset.Max
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Base multiplicities of strict transforms

On a smooth integral surface, the moving-ideal transform of an effective
Cartier divisor is its scheme-theoretic strict transform. The comparison
relates incidence on successive transforms to the first blowup over a point
of the original surface. In particular, a maximal base multiplicity on the
divisor can be realized by a proper center, with ties settled by tower order.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k]
  {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
  {C : X.IdealSheafData} (hC : C.IsEffectiveCartier)

include f hC in
/-- Iterated removal of the exceptional powers of an effective Cartier ideal gives its
scheme-theoretic strict transform. -/
theorem movingBaseIdeal_eq_strictTransform :
    hT.movingBaseIdeal C = T.strictTransform C := by
  induction hT with
  | nil => simp
  | @snoc d W U I hU p hp hI ih =>
    let g := U.toBase ≫ f
    have : IsIntegral W := hU.isIntegral f
    have : IsNoetherian W := U.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hU.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp
      inferInstance).2 p hp
    have hstep :=
      (hU.isEffectiveCartier_strictTransform f hC).comap_blowupToBase_colon_eq_strictTransform hp hd
    rw [movingBaseIdeal_snoc hU C p hp hI, strictTransform_snoc, ih, hI,
      W.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact hstep

include f hC in
/-- In the marking by total exceptional classes, the coefficients of a strict
transform are the negatives of the successive multiplicities of the divisor. -/
theorem strictTransformCoefficients_eq_neg_baseMultiplicities (j : Fin n) :
    hT.strictTransformCoefficients C j = -(hT.baseMultiplicities C j : ℤ) := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d W U I hU p hp hI ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [strictTransformCoefficients_snoc_last C _ p hp hI,
        baseMultiplicities_snoc_last hU C p hp hI, hU.movingBaseIdeal_eq_strictTransform f hC]
    · simpa only [strictTransformCoefficients_snoc_castSucc, baseMultiplicities_snoc_castSucc]
        using ih j

include f hC in
/-- The image of a center with a nonzero strict-transform coefficient lies on the
original divisor. -/
theorem baseCenter_mem_support_of_strictTransformCoefficients_ne_zero {j : Fin n}
    (hj : hT.strictTransformCoefficients C j ≠ 0) :
    hT.baseCenter j ∈ C.support := by
  by_contra hmiss
  have habove := hT.baseMultiplicities_le_stalkOrder_baseCenter f C j
  rw [(C.stalkOrder_eq_zero_iff _).mpr hmiss] at habove
  have hz : hT.baseMultiplicities C j = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp habove)
  exact hj (by rw [hT.strictTransformCoefficients_eq_neg_baseMultiplicities f hC, hz,
    Int.natCast_zero, neg_zero])

include f hC in
/-- At the first blowup over a point, incidence with the current strict transform
is equivalent to incidence of the projected center with the original divisor. -/
theorem strictTransformCoefficients_ne_zero_iff_of_first {j : Fin n}
    (hj : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) :
    hT.strictTransformCoefficients C j ≠ 0 ↔ hT.baseCenter j ∈ C.support := by
  refine ⟨hT.baseCenter_mem_support_of_strictTransformCoefficients_ne_zero f hC, fun hm hz ↦ ?_⟩
  rw [hT.strictTransformCoefficients_eq_neg_baseMultiplicities f hC,
    hT.baseMultiplicities_eq_stalkOrder_toNat_of_first C j hj, neg_eq_zero,
    Int.natCast_eq_zero] at hz
  have hfin : C.stalkOrder (hT.baseCenter j) ≠ ⊤ := by
    rw [stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hC.stalkIdeal_ne_bot _
  exact ((C.stalkOrder_eq_zero_iff _).mp (ENat.toNat_eq_zero.mp hz |>.resolve_right hfin)) hm

variable {J : X.IdealSheafData}

include f hC in
/-- The earliest center of maximal base multiplicity along successive strict
transforms is the first center over its image on the original surface. Its
image belongs to the original divisor. -/
theorem exists_first_max_baseMultiplicity_on_strictTransform (hJ : J ≠ ⊥)
    (hne : ∃ j, hT.strictTransformCoefficients C j ≠ 0) :
    ∃ i : Fin n, hT.strictTransformCoefficients C i ≠ 0 ∧
      (∀ j, hT.strictTransformCoefficients C j ≠ 0 →
        hT.baseMultiplicities J j ≤ hT.baseMultiplicities J i) ∧
      (∀ j < i, hT.strictTransformCoefficients C j ≠ 0 →
        hT.baseMultiplicities J j < hT.baseMultiplicities J i) ∧
      (∀ j < i, hT.baseCenter j ≠ hT.baseCenter i) ∧ hT.baseCenter i ∈ C.support := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun j ↦ hT.strictTransformCoefficients C j ≠ 0)
  have hA (j) : j ∈ A ↔ hT.strictTransformCoefficients C j ≠ 0 := by simp [A]
  obtain ⟨i, hi, hmax⟩ := A.exists_max_image (hT.baseMultiplicities J)
    (by simpa only [Finset.Nonempty, hA] using hne)
  let B := {j ∈ (A : Set (Fin n)) | hT.baseMultiplicities J j = hT.baseMultiplicities J i}
  obtain ⟨a, ⟨ha, hva⟩, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min B ⟨i, hi, rfl⟩
  have hbound (j) (hj : hT.strictTransformCoefficients C j ≠ 0) :
      hT.baseMultiplicities J j ≤ hT.baseMultiplicities J a :=
    (hmax j ((hA j).mpr hj)).trans_eq hva.symm
  have hstrict (j) (hj : j < a) (hmem : hT.strictTransformCoefficients C j ≠ 0) :
      hT.baseMultiplicities J j < hT.baseMultiplicities J a :=
    lt_of_le_of_ne (hbound j hmem) fun he ↦ hmin j ⟨(hA j).mpr hmem, he.trans hva⟩ hj
  have hmem := hT.baseCenter_mem_support_of_strictTransformCoefficients_ne_zero
    f hC ((hA a).mp ha)
  refine ⟨a, (hA a).mp ha, hbound, hstrict, ?_, hmem⟩
  -- The first center over the same point is also incident and has at least this order.
  let D := {j | hT.baseCenter j = hT.baseCenter a}
  obtain ⟨l, (hl : hT.baseCenter l = hT.baseCenter a), hlo⟩ :=
    (wellFounded_lt (α := Fin n)).has_min D ⟨a, rfl⟩
  have hlfirst (j) (hj : j < l) : hT.baseCenter j ≠ hT.baseCenter l :=
    fun he ↦ hlo j (he.trans hl) hj
  have hlmem := (hT.strictTransformCoefficients_ne_zero_iff_of_first f hC hlfirst).mpr (hl ▸ hmem)
  have hlle := hT.baseMultiplicities_le_of_first_baseCenter f J hJ hl hlfirst
  have heq : l = a := le_antisymm (le_of_not_gt (hlo a rfl))
    (le_of_not_gt fun hlt ↦ (not_lt_of_ge hlle) (hstrict l hlt hlmem))
  simpa only [heq] using hlfirst

end QPainleve.BlowupTower.IsClosedPointTower
