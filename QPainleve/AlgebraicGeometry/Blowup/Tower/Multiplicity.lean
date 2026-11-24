/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.MovingBaseIdeal

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Order
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Proper base points of high multiplicity

On a tower of closed point blowups, the order of the moving base ideal at a
closed point is bounded by the order of the original ideal at its image.
Thus a large multiplicity in the resolved linear system supplies a proper
base point for a Sarkisov link, as used in
[Lutz's appendix to Hacking and Keating, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X] {n : ℕ} {T : BlowupTower X n Y}
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

/-- A positive multiplicity at any center of a closed point tower gives a
proper base point of at least that multiplicity on the starting surface. -/
theorem exists_base_point_stalkOrder_ge_baseMultiplicity
    (hT : IsClosedPointTower X T) (J : X.IdealSheafData) (j : Fin n)
    (hj : 0 < hT.baseMultiplicities J j) :
    ∃ p : X, IsClosed ({p} : Set X) ∧ p ∈ J.support ∧
      (hT.baseMultiplicities J j : ℕ∞) ≤ J.stalkOrder p := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d W S I hS p hp hI ih =>
    refine Fin.lastCases ?_ (fun l ↦ ?_) j hj
    · rw [baseMultiplicities_snoc_last hS J p hp hI]
      intro hm
      have : IsProper S.toBase := S.isProper_toBase
      have hc : IsClosed ({S.toBase p} : Set X) := by
        simpa only [Set.image_singleton] using S.toBase.isClosedMap _ hp
      have hle := (ENat.natCast_toNat_le_self _).trans (hS.stalkOrder_movingBaseIdeal_le f J hp)
      refine ⟨S.toBase p, hc, (one_le_stalkOrder_iff J _).mp ?_, hle⟩
      exact (by exact_mod_cast hm : (1 : ℕ∞) ≤ _).trans hle
    · simpa only [baseMultiplicities_snoc_castSucc] using ih l

end QPainleve.BlowupTower.IsClosedPointTower
