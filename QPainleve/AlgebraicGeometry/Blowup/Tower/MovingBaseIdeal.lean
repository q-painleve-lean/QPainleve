/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Multiplicity
import QPainleve.AlgebraicGeometry.Blowup.LinearSystem
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Base multiplicities on a point blowup tower

The transform of a base ideal at each stage removes the exceptional power of its order
at the current point. Tracking these powers on the actual schemes gives the Picard
marking of a resolved moving system, including multiplicities at infinitely near centers.
This is the iterated moving-system transform of Hacking, *583C Lecture notes*,
Proposition 7.3.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

/-- The base ideal after removing at each stage the common exceptional power of the current
base ideal. If the original ideal has no fixed components, this is the base ideal of the
moving system on the final scheme. -/
def movingBaseIdeal (J : X.IdealSheafData) :
    {n : ℕ} → {Y : Scheme.{u}} → {T : BlowupTower X n Y} →
      IsClosedPointTower X T → Y.IdealSheafData
  | _, _, .nil, _ => J
  | _, _, .snoc _ I, h =>
    let B := movingBaseIdeal J (snoc_iff.mp h).1
    (B.comap I.blowupToBase).colon
      ((I.comap I.blowupToBase) ^ (B.stalkOrder h.lastCenter.val).toNat)

@[simp]
theorem movingBaseIdeal_nil (J : X.IdealSheafData) :
    (nil (X := X)).movingBaseIdeal J = J := (rfl)

/-- At the last blowup the transform is the total transform divided by the exceptional power
of the order before that blowup. -/
theorem movingBaseIdeal_snoc (hT : IsClosedPointTower X T) (J : X.IdealSheafData)
    (p : Y) (hp : IsClosed ({p} : Set Y)) {I : Y.IdealSheafData}
    (hI : I = (Y.fromSpecResidueField p).ker) :
    (hT.snoc p hp hI).movingBaseIdeal J =
      ((hT.movingBaseIdeal J).comap I.blowupToBase).colon
        ((I.comap I.blowupToBase) ^ ((hT.movingBaseIdeal J).stalkOrder p).toNat) := by
  simp only [movingBaseIdeal, lastCenter_eq _ p hp hI]

/-- The multiplicities of the successive base ideals at the actual blowup centers. -/
def baseMultiplicities (J : X.IdealSheafData) :
    {n : ℕ} → {Y : Scheme.{u}} → {T : BlowupTower X n Y} →
      IsClosedPointTower X T → Fin n → ℕ
  | _, _, .nil, _ => Fin.elim0
  | _, _, .snoc _ _, h =>
    let hT := (snoc_iff.mp h).1
    Fin.lastCases ((hT.movingBaseIdeal J).stalkOrder h.lastCenter.val).toNat
      (baseMultiplicities J hT)

/-- Appending a blowup preserves each earlier base multiplicity. -/
@[simp]
theorem baseMultiplicities_snoc_castSucc (J : X.IdealSheafData)
    {I : Y.IdealSheafData} (h : IsClosedPointTower X (T.snoc I)) (j : Fin n) :
    h.baseMultiplicities J j.castSucc = (snoc_iff.mp h).1.baseMultiplicities J j := by
  simp only [baseMultiplicities, Fin.lastCases_castSucc]

/-- The last multiplicity is the order of the moving base ideal immediately before the
last blowup. -/
theorem baseMultiplicities_snoc_last (hT : IsClosedPointTower X T) (J : X.IdealSheafData)
    (p : Y) (hp : IsClosed ({p} : Set Y)) {I : Y.IdealSheafData}
    (hI : I = (Y.fromSpecResidueField p).ker) :
    (hT.snoc p hp hI).baseMultiplicities J (Fin.last n) =
      ((hT.movingBaseIdeal J).stalkOrder p).toNat := by
  simp only [baseMultiplicities, Fin.lastCases_last, lastCenter_eq _ p hp hI]

private def removedBaseIdeal (J : X.IdealSheafData) :
    {n : ℕ} → {Y : Scheme.{u}} → {T : BlowupTower X n Y} →
      IsClosedPointTower X T → Y.IdealSheafData
  | _, _, .nil, _ => ⊤
  | _, _, .snoc _ I, h =>
    (removedBaseIdeal J (snoc_iff.mp h).1).comap I.blowupToBase *
      (I.comap I.blowupToBase) ^ h.baseMultiplicities J (Fin.last _)

private theorem removedBaseIdeal_snoc (hT : IsClosedPointTower X T) (J : X.IdealSheafData)
    (p : Y) (hp : IsClosed ({p} : Set Y)) {I : Y.IdealSheafData}
    (hI : I = (Y.fromSpecResidueField p).ker) :
    (hT.snoc p hp hI).removedBaseIdeal J =
      (hT.removedBaseIdeal J).comap I.blowupToBase *
        (I.comap I.blowupToBase) ^ ((hT.movingBaseIdeal J).stalkOrder p).toNat := by
  rw [removedBaseIdeal.eq_2, baseMultiplicities_snoc_last hT J p hp hI]

private theorem comap_eq_movingBaseIdeal_mul (hT : IsClosedPointTower X T)
    (J : X.IdealSheafData) :
    J.comap T.toBase = hT.movingBaseIdeal J * hT.removedBaseIdeal J := by
  induction hT with
  | nil => simp [removedBaseIdeal]
  | snoc hS p hp hI ih =>
    subst hI
    rw [toBase_snoc, comap_comp, ih, comap_mul, removedBaseIdeal_snoc hS J p hp rfl,
      movingBaseIdeal_snoc hS J p hp rfl,
      mul_comm ((hS.removedBaseIdeal J).comap _) _, ← mul_assoc,
      ← comap_blowupToBase_eq_colon_mul_exceptional_pow p hp]

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [hf : SmoothOfRelativeDimension 2 f]

include f hf

private theorem isEffectiveCartier_removedBaseIdeal (hT : IsClosedPointTower X T)
    (J : X.IdealSheafData) : (hT.removedBaseIdeal J).IsEffectiveCartier := by
  induction hT with
  | nil => exact isEffectiveCartier_top X
  | @snoc d W S I hS p hp hI ih =>
    let hlast := (nil (X := W)).snoc p hp hI
    let g := S.toBase ≫ f
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : IsIntegral I.blowup := hlast.isIntegral g
    have : Surjective I.blowupToBase := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hlast.surjective g
    rw [removedBaseIdeal_snoc hS J p hp hI]
    exact TauCeti.isEffectiveCartier_mul (ih.comap_of_isDominant _)
      (TauCeti.isEffectiveCartier_pow I.isEffectiveCartier_comap_blowupToBase _)

private theorem movingBaseIdeal_ne_bot_and_no_divisorial_support
    (hT : IsClosedPointTower X T) {J : X.IdealSheafData} (hJ : J ≠ ⊥)
    (hmove : ∀ x : CodimensionOnePoint X, (x : X) ∉ J.support) :
    hT.movingBaseIdeal J ≠ ⊥ ∧
      ∀ y : CodimensionOnePoint Y, (y : Y) ∉ (hT.movingBaseIdeal J).support := by
  induction hT with
  | nil => exact ⟨hJ, hmove⟩
  | @snoc d W S I hS p hp hI ih =>
    subst I
    let g := S.toBase ≫ f
    let J' := hS.movingBaseIdeal J
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have hfin := J'.stalkOrder_lt_top_of_ne_bot ih.1 p
    refine ⟨?_, ?_⟩
    · intro he
      rw [movingBaseIdeal_snoc hS J p hp rfl] at he
      have ht := comap_blowupToBase_eq_colon_mul_exceptional_pow p hp J'
      rw [he, bot_mul, ← le_bot_iff, ← le_map_iff_comap_le, map_bot] at ht
      have : Surjective (W.fromSpecResidueField p).ker.blowupToBase := by
        rw [W.ker_fromSpecResidueField_eq_vanishingIdeal]
        exact surjective_blowupToBase_point hp hd
      have := IsSchemeTheoreticallyDominant.of_isDominant
        (W.fromSpecResidueField p).ker.blowupToBase
      rw [Scheme.Hom.ker_eq_bot, le_bot_iff] at ht
      exact ih.1 ht
    · rw [movingBaseIdeal_snoc hS J p hp rfl]
      exact notMem_support_comap_blowupToBase_colon_exceptional_pow p hp hd J' ih.2 _
        (ENat.natCast_toNat hfin.ne).symm

/-- A point tower that principalizes a base ideal without fixed components removes its
whole base ideal by successive exceptional division. -/
theorem movingBaseIdeal_eq_top (hT : IsClosedPointTower X T) {J : X.IdealSheafData}
    (hmove : ∀ x : CodimensionOnePoint X, (x : X) ∉ J.support)
    (hJ : (J.comap T.toBase).IsEffectiveCartier) : hT.movingBaseIdeal J = ⊤ := by
  have : IsIntegral Y := hT.isIntegral f
  have : IsNoetherian Y := T.isNoetherian
  have hne : J ≠ ⊥ := by
    intro he
    exact hJ.stalkIdeal_ne_bot (genericPoint Y) (by simp [he])
  have hsupport := (hT.movingBaseIdeal_ne_bot_and_no_divisorial_support f hne hmove).2
  have hfac := hT.comap_eq_movingBaseIdeal_mul J
  have hE := hT.isEffectiveCartier_removedBaseIdeal f J
  have hc : (hT.movingBaseIdeal J).IsEffectiveCartier := by
    rw [hfac] at hJ
    simpa only [hE.mul_colon_cancel_right] using hJ.colon hE.locallyPrincipal
      (by intro U; exact Ideal.mul_le_right)
  apply (support_eq_bot_iff _).mp
  exact le_bot_iff.mp fun y hy ↦ by
    obtain ⟨q, hq, -⟩ := hc.mem_support_iff_exists_codimensionOnePoint.mp hy
    exact (hsupport q hq).elim

private theorem picardHom_removedBaseIdeal (hT : IsClosedPointTower X T)
    (J : X.IdealSheafData) (a : LineBundleClass X) :
    (T.picardHom (Additive.ofMul a, fun j ↦ -(hT.baseMultiplicities J j : ℤ))).toMul =
      pullback T.toBase a * mk (hT.isEffectiveCartier_removedBaseIdeal f J).toInvertibleSheaf := by
  induction hT with
  | nil => simp [removedBaseIdeal]
  | @snoc d W S I hS p hp hI ih =>
    let hE := TauCeti.isEffectiveCartier_pow I.isEffectiveCartier_comap_blowupToBase
      ((hS.movingBaseIdeal J).stalkOrder p).toNat
    let hF := hS.isEffectiveCartier_removedBaseIdeal f J
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 (S.toBase ≫ f) := hS.smoothOfRelativeDimension f
    let hlast := (nil (X := W)).snoc p hp hI
    have : IsIntegral I.blowup := hlast.isIntegral (S.toBase ≫ f)
    have : Surjective I.blowupToBase := by
      simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hlast.surjective (S.toBase ≫ f)
    let hP := hF.comap_of_isDominant I.blowupToBase
    rw [picardHom_snoc_apply_toMul]
    simp only [baseMultiplicities_snoc_castSucc]
    rw [ih, baseMultiplicities_snoc_last hS J p hp hI, blowupExceptionalClass_def,
      zpow_neg, zpow_natCast, inv_pow, inv_inv, toBase_snoc, pullback_mul, ← pullback_comp,
      mul_assoc,
      mk_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_mul hP hE)
        (removedBaseIdeal_snoc hS J p hp hI),
      mk_toInvertibleSheaf_mul hP hE, hF.pullback_mk_toInvertibleSheaf hP,
      mk_toInvertibleSheaf_pow]

/-- After principalization of a base ideal without fixed components, twisting the pullback
of the original line class by the total base ideal has the original base coordinate and
the negatives of the successive base multiplicities as exceptional coordinates. -/
theorem picardHom_movingBaseIdeal (hT : IsClosedPointTower X T) {J : X.IdealSheafData}
    (hmove : ∀ x : CodimensionOnePoint X, (x : X) ∉ J.support)
    (hJ : (J.comap T.toBase).IsEffectiveCartier) (a : LineBundleClass X) :
    (T.picardHom (Additive.ofMul a, fun j ↦ -(hT.baseMultiplicities J j : ℤ))).toMul =
      pullback T.toBase a * mk hJ.toInvertibleSheaf := by
  rw [hT.picardHom_removedBaseIdeal f J a]
  apply congrArg (pullback T.toBase a * ·)
  apply mk_toInvertibleSheaf_congr
  rw [hT.comap_eq_movingBaseIdeal_mul J, hT.movingBaseIdeal_eq_top f hmove hJ, top_mul]

end QPainleve.BlowupTower.IsClosedPointTower
