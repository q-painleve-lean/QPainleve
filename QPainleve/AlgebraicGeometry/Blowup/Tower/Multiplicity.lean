/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.MovingBaseIdeal
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Order
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Proper base points of high multiplicity

On a tower of closed point blowups, the order of the moving base ideal at a
closed point is bounded by the order of the original ideal at its image.
At the first center over the image the orders agree. Moving this center to the front
of the tower makes the proper base point available for a Sarkisov link, as used in
[Lutz's appendix to Hacking and Keating, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}

private theorem stalkOrder_movingBaseIdeal_eq_of_notMem_range_baseCenter
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (y : Y)
    (h : T.toBase y ∉ Set.range hT.baseCenter) :
    (hT.movingBaseIdeal J).stalkOrder y = J.stalkOrder (T.toBase y) := by
  induction hT with
  | nil => simp
  | @snoc n W T I hT q hq hI ih =>
    subst I
    let π := (W.fromSpecResidueField q).ker.blowupToBase
    have hy : π y ≠ q := by
      intro he
      exact h ⟨Fin.last n, by
        rw [baseCenter_snoc_last, lastCenter_eq _ q hq rfl, toBase_snoc,
          Scheme.Hom.comp_apply, he]⟩
    have hy' : T.toBase (π y) ∉ Set.range hT.baseCenter := by
      rintro ⟨i, hi⟩
      exact h ⟨i.castSucc, by simpa only [baseCenter_snoc_castSucc, toBase_snoc,
        Scheme.Hom.comp_apply] using hi⟩
    rw [movingBaseIdeal_snoc hT J q hq rfl, toBase_snoc, Scheme.Hom.comp_apply,
      stalkOrder_colon_exceptional_pow_eq_of_ne q hq _ hy, ih _ hy']

/-- The first blowup over a base point has the multiplicity of the original ideal
at that point. Every earlier center lies over a different point. -/
theorem baseMultiplicities_eq_stalkOrder_toNat_of_first
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (j : Fin n)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j) :
    hT.baseMultiplicities J j = (J.stalkOrder (hT.baseCenter j)).toNat := by
  induction hT with
  | nil => exact j.elim0
  | @snoc n W T I hT q hq hI ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j hj
    · intro h
      rw [baseMultiplicities_snoc_last hT J q hq hI, baseCenter_snoc_last,
        lastCenter_eq _ q hq hI, hT.stalkOrder_movingBaseIdeal_eq_of_notMem_range_baseCenter]
      rintro ⟨i, hi⟩
      exact h i.castSucc (Fin.castSucc_lt_last i) (by
        simpa only [baseCenter_snoc_castSucc, baseCenter_snoc_last, lastCenter_eq _ q hq hI]
          using hi)
    · intro hi
      rw [baseMultiplicities_snoc_castSucc, baseCenter_snoc_castSucc]
      exact ih i fun l hl ↦ by
        simpa only [baseCenter_snoc_castSucc] using (hi l.castSucc
          (Fin.castSucc_lt_castSucc_iff.mpr hl))

variable {k : Type u} [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [hf : SmoothOfRelativeDimension 2 f]

include f hf

/-- The order after the successive exceptional divisions at a closed point on a
tower is at most the original order at its image on the surface. -/
theorem stalkOrder_movingBaseIdeal_le (hT : IsClosedPointTower X T) (J : X.IdealSheafData)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    (hT.movingBaseIdeal J).stalkOrder y ≤ J.stalkOrder (T.toBase y) := by
  induction hT with
  | nil => simp
  | @snoc d W S I hS p hp hI ih =>
    subst I
    let g := S.toBase ≫ f
    let I := (W.fromSpecResidueField p).ker
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp
      inferInstance).2 p hp
    have hc : IsClosed ({I.blowupToBase y} : Set W) := by
      simpa only [Set.image_singleton] using I.blowupToBase.isClosedMap _ hy
    rw [movingBaseIdeal_snoc hS J p hp rfl, toBase_snoc, Scheme.Hom.comp_apply]
    refine le_trans ?_ (ih hc)
    by_cases h : I.blowupToBase y = p
    · rw [h]
      exact stalkOrder_colon_exceptional_pow_le p hp hdim (hS.movingBaseIdeal J) hy h
    · exact (stalkOrder_colon_exceptional_pow_eq_of_ne p hp (hS.movingBaseIdeal J) h).le

/-- Every successive multiplicity is bounded by the original order at its projected center. -/
theorem baseMultiplicities_le_stalkOrder_baseCenter
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (j : Fin n) :
    (hT.baseMultiplicities J j : ℕ∞) ≤ J.stalkOrder (hT.baseCenter j) := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d W S I hS p hp hI ih =>
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · rw [baseMultiplicities_snoc_last hS J p hp hI, baseCenter_snoc_last,
        lastCenter_eq _ p hp hI]
      exact (ENat.natCast_toNat_le_self _).trans (hS.stalkOrder_movingBaseIdeal_le f J hp)
    · simpa only [baseMultiplicities_snoc_castSucc, baseCenter_snoc_castSucc] using ih l

/-- A positive multiplicity at any center of a closed point tower gives a
proper base point of at least that multiplicity on the starting surface. -/
theorem exists_base_point_stalkOrder_ge_baseMultiplicity
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (j : Fin n)
    (hj : 0 < hT.baseMultiplicities J j) :
    ∃ p : X, IsClosed ({p} : Set X) ∧ p ∈ J.support ∧
      (hT.baseMultiplicities J j : ℕ∞) ≤ J.stalkOrder p := by
  have hle := hT.baseMultiplicities_le_stalkOrder_baseCenter f J j
  refine ⟨hT.baseCenter j, hT.isClosed_baseCenter j, (one_le_stalkOrder_iff J _).mp ?_, hle⟩
  exact (by exact_mod_cast hj : (1 : ℕ∞) ≤ _).trans hle

/-- Move the first blowup over the projected center to the front of the same resolution.
Its order is at least the given order, and the isomorphism matches every total exceptional
class in the reordered marking. -/
theorem exists_move_base_point_blowup_to_front {T : BlowupTower X (n + 1) Y}
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (hJ : J ≠ ⊥) (j : Fin (n + 1)) :
    let p := hT.baseCenter j
    let I := (X.fromSpecResidueField p).ker
    ∃ (i : Fin (n + 1)) (W : Scheme.{u}) (U : BlowupTower I.blowup n W) (e : Y ≅ W),
      IsLeast {l | hT.baseCenter l = p} i ∧
      hT.baseMultiplicities J j ≤ hT.baseMultiplicities J i ∧
      hT.baseMultiplicities J i = (J.stalkOrder p).toNat ∧
      IsClosedPointTower I.blowup U ∧ e.hom ≫ U.toBase ≫ I.blowupToBase = T.toBase ∧
      pullback e.hom (pullback U.toBase I.blowupExceptionalClass) = T.exceptionalClass i ∧
      ∀ l : Fin n, pullback e.hom (U.exceptionalClass l) = T.exceptionalClass (i.succAbove l) := by
  let p := hT.baseCenter j
  obtain ⟨i, hi, hfirst⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min
    {i | hT.baseCenter i = p} ⟨j, rfl⟩
  have hip : hT.baseCenter i = p := hi
  have hp := hT.isClosed_baseCenter j
  have hprevious (l : Fin (n + 1)) (hl : l < i) : hT.baseCenter l ≠ p :=
    fun he ↦ hfirst l he hl
  have horder := hT.baseMultiplicities_eq_stalkOrder_toNat_of_first J i fun l hl he ↦
    hprevious l hl (he.trans hip)
  rw [hip] at horder
  have hle := ENat.toNat_le_toNat (hT.baseMultiplicities_le_stalkOrder_baseCenter f J j)
    (J.stalkOrder_lt_top_of_ne_bot hJ p).ne
  have hle' : hT.baseMultiplicities J j ≤ hT.baseMultiplicities J i := by
    rw [horder]
    simpa only [ENat.toNat_natCast] using hle
  obtain ⟨W, U, e, he⟩ := hT.exists_move_closed_point_blowup_to_front i hp hip hprevious
  exact ⟨i, W, U, e, ⟨hi, fun l hl ↦ le_of_not_gt (hfirst l hl)⟩, hle', horder, he⟩

end QPainleve.BlowupTower.IsClosedPointTower
