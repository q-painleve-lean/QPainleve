/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

import QPainleve.AlgebraicGeometry.Blowup.Order
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Pole divisors along a point blowup tower

For a top form with pole divisor `D` and no zeros on the base, the pullback has
no zeros precisely when the ideal of the total transform of `D` is contained
in the ramification ideal. This condition descends to every prefix. Consequently
every blowup center is on the current pole divisor, and the new pole divisor is
its strict transform plus the exceptional divisor with multiplicity `m - 1`,
where `m` is the order at the center.

The exclusion of centers outside the pole divisor is used in the factorization
of volume-preserving maps in Hacking and Keating, *Homological mirror symmetry
for log Calabi–Yau surfaces*, Appendix by Lutz, [Definition 8.1 and Theorem 8.4].

[Definition 8.1 and Theorem 8.4]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n m : ℕ} {T : BlowupTower X n Y} {U : BlowupTower Y m Z}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData}

private theorem totalTransform_le_ramification_of_snoc (hD : D.IsEffectiveCartier)
    (hT : IsClosedPointTower X T) {I : Y.IdealSheafData}
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker)
    (h : D.comap (T.snoc I).toBase ≤ (hT.snoc p hp hI).ramificationIdealSheafToBase k) :
    D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k := by
  let s := X ↘ Spec (.of k)
  let t := T.toBase ≫ s
  let V := BlowupTower.nil.snoc I
  have hV : IsClosedPointTower Y V := IsClosedPointTower.nil.snoc p hp hI
  have : IsIntegral Y := hT.isIntegral s
  have : IsNoetherian Y := T.isNoetherian
  have : SmoothOfRelativeDimension 2 t := hT.smoothOfRelativeDimension s
  have : Smooth t := SmoothOfRelativeDimension.smooth 2 t
  have : IsRegular Y := IsRegular.of_smooth t
  have : IsIntegral I.blowup := hV.isIntegral t
  have : IsModification I.blowupToBase := by
    simpa only [V, toBase_snoc, toBase_nil, Category.comp_id] using
      hV.isModification_of_smoothOfRelativeDimension_two t
  have hRam := hT.isEffectiveCartier_ramificationIdealSheafToBase k
  have hTotal := hT.isEffectiveCartier_totalTransform s hD
  apply (hTotal.comap_le_comap_iff_of_isModification I.blowupToBase hRam).mp
  rw [toBase_snoc, comap_comp, ramificationIdealSheafToBase_snoc k (hT.snoc p hp hI)] at h
  exact h.trans fun _ ↦ Ideal.mul_le_right

/-- If the pullback of a top form with pole divisor `D` has no zeros at the top of a
point tower, it has no zeros after any prefix. The condition is expressed as inclusion
of the total-transform ideal in the ramification ideal. -/
theorem totalTransform_le_ramification_of_append (hD : D.IsEffectiveCartier)
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    (h : D.comap (T.append U).toBase ≤ (hT.append hU).ramificationIdealSheafToBase k) :
    D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k := by
  induction hU with
  | nil => simpa only [append_nil] using h
  | @snoc _ W V I hV p hp hI ih =>
    apply ih
    exact totalTransform_le_ramification_of_snoc k hD (hT.append hV) p hp hI
      (by simpa only [append_snoc] using h)

private theorem comap_poleIdeal_le_exceptional_of_snoc (hD : D.IsEffectiveCartier)
    (hT : IsClosedPointTower X T) {I : Y.IdealSheafData}
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker)
    (h : D.comap (T.snoc I).toBase ≤ (hT.snoc p hp hI).ramificationIdealSheafToBase k) :
    let R := hT.ramificationIdealSheafToBase k
    let P := (D.comap T.toBase).colon R
    P.IsEffectiveCartier ∧ D.comap T.toBase = P * R ∧
      P.comap I.blowupToBase ≤ I.comap I.blowupToBase := by
  dsimp only
  let s := X ↘ Spec (.of k)
  let t := T.toBase ≫ s
  let R := hT.ramificationIdealSheafToBase k
  let P := (D.comap T.toBase).colon R
  let π := I.blowupToBase
  let E := I.comap π
  have hR := hT.isEffectiveCartier_ramificationIdealSheafToBase k
  have hTotal := hT.isEffectiveCartier_totalTransform s hD
  have hle := totalTransform_le_ramification_of_snoc k hD hT p hp hI h
  have hP := hTotal.colon hR.locallyPrincipal hle
  have hfac : D.comap T.toBase = P * R := (D.comap T.toBase).eq_colon_mul R hR.locallyPrincipal hle
  have : IsIntegral Y := hT.isIntegral s
  have : IsNoetherian Y := T.isNoetherian
  have : SmoothOfRelativeDimension 2 t := hT.smoothOfRelativeDimension s
  let V := BlowupTower.nil.snoc I
  have hV : IsClosedPointTower Y V := IsClosedPointTower.nil.snoc p hp hI
  have hRπ : (R.comap π).IsEffectiveCartier := by
    simpa only [V, π, toBase_snoc, toBase_nil, Category.comp_id] using
      hV.isEffectiveCartier_totalTransform t hR
  rw [toBase_snoc, comap_comp, hfac, comap_mul,
    ramificationIdealSheafToBase_snoc k (hT.snoc p hp hI)] at h
  have hcancel := Scheme.IdealSheafData.colon_mono h (le_rfl : R.comap π ≤ R.comap π)
  rw [hRπ.mul_colon_cancel_right, hRπ.mul_colon_cancel_right] at hcancel
  exact ⟨hP, hfac, hcancel⟩

/-- In a tower whose composite pullback has no zeros, the last center lies on the
pole divisor of the preceding stage. The final pole ideal is the ideal of its strict
transform times the exceptional ideal raised to the order at the center minus one. -/
theorem poleIdeal_snoc_of_totalTransform_le_ramification (hD : D.IsEffectiveCartier)
    (hT : IsClosedPointTower X T) {I : Y.IdealSheafData}
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker)
    (h : D.comap (T.snoc I).toBase ≤ (hT.snoc p hp hI).ramificationIdealSheafToBase k) :
    let R := hT.ramificationIdealSheafToBase k
    let P := (D.comap T.toBase).colon R
    let R' := (hT.snoc p hp hI).ramificationIdealSheafToBase k
    let E := I.comap I.blowupToBase
    P.IsEffectiveCartier ∧ p ∈ P.support ∧
      (D.comap (T.snoc I).toBase).colon R' =
        (I.blowupMap P.subschemeι).ker * E ^ ((P.stalkOrder p).toNat - 1) := by
  let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
  let t := T.toBase ≫ (X ↘ Spec (.of k))
  have : IsIntegral Y := hT.isIntegral (X ↘ Spec (.of k))
  have : IsNoetherian Y := T.isNoetherian
  have : SmoothOfRelativeDimension 2 t := hT.smoothOfRelativeDimension _
  have : Smooth t := SmoothOfRelativeDimension.smooth 2 t
  have : IsRegular Y := IsRegular.of_smooth t
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq t 2).mp inferInstance).2 p hp
  obtain ⟨hP, hfac, hle⟩ := comap_poleIdeal_le_exceptional_of_snoc k hD hT p hp hI h
  have hcenter := hI.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal p)
  have hpos : 1 ≤ P.stalkOrder p :=
    (comap_blowupToBase_le_exceptional_pow_iff p hp hdim P 1).mp (by
      rw [pow_one, ← hI]
      exact hle)
  refine ⟨hP, (P.one_le_stalkOrder_iff p).mp hpos, ?_⟩
  have hm : 1 ≤ (P.stalkOrder p).toNat := ENat.toNat_le_toNat hpos (by
    rw [P.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hP.stalkIdeal_ne_bot p)
  have hsplit : P.comap I.blowupToBase =
      (I.blowupMap P.subschemeι).ker * (I.comap I.blowupToBase) ^ (P.stalkOrder p).toNat := by
    have hsplit := hP.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hdim
    rw [← hcenter] at hsplit
    exact hsplit
  let C := (I.blowupMap P.subschemeι).ker * (I.comap I.blowupToBase) ^ ((P.stalkOrder p).toNat - 1)
  have heq : P.comap I.blowupToBase = C * (I.comap I.blowupToBase) := by
    rw [hsplit, mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]
  let R := hT.ramificationIdealSheafToBase k
  let R' := (hT.snoc p hp hI).ramificationIdealSheafToBase k
  let π := I.blowupToBase
  have htop : D.comap (T.snoc I).toBase = C * R' := by
    calc
      _ = (P * R).comap π := by
        rw [toBase_snoc, comap_comp]
        exact congrArg (·.comap π) hfac
      _ = _ := by
        rw [comap_mul, heq, mul_assoc]
        exact congrArg (C * ·) (ramificationIdealSheafToBase_snoc k (hT.snoc p hp hI)).symm
  have hR' := (hT.snoc p hp hI).isEffectiveCartier_ramificationIdealSheafToBase k
  rw [htop, hR'.mul_colon_cancel_right]

end QPainleve.BlowupTower.IsClosedPointTower
