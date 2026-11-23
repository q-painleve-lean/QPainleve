/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Restriction of marked blowup classes to a fixed boundary

The total exceptional class at each stage of an ordered boundary blowup tower restricts
to the positive Cartier class of its prescribed center on the original boundary. This
gives a restriction formula in Picard coordinates, even for repeated centers.

For internal blowups of an anticanonical cycle, this is the exceptional-divisor
restriction used in Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical
cycle*, Proposition 2.9. The scheme-theoretic intersection at a single stage is
`WithBoundary.comap_exceptional_boundaryι_snoc`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace QPainleve.BlowupTower

variable {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] {n : ℕ}
  (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})

/-- The total exceptional line bundle at label `j` restricts along the final boundary
embedding to the inverse of the ideal line bundle of the original center. -/
@[simp]
theorem pullback_exceptionalClass_alongBoundary (j : Fin n) :
    pullback (alongBoundary i J).2.boundaryι ((alongBoundary i J).2.toTower.exceptionalClass j) =
      (mk (J j).property.toInvertibleSheaf)⁻¹ := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    -- The source of the line-bundle pullback depends on the ordered model.
    let P (M : Σ Y, WithBoundary i (n + 1) Y) : Prop :=
      pullback M.2.boundaryι (M.2.toTower.exceptionalClass j) =
        (mk (J j).property.toInvertibleSheaf)⁻¹
    refine (congrArg P (alongBoundary_succ i J)).mpr ?_
    let T := (alongBoundary i (fun k ↦ J k.castSucc)).2
    let C := J (Fin.last n)
    dsimp only [P, Sigma.snd]
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [WithBoundary.toTower_snoc, exceptionalClass_snoc_last, pullback_inv]
      let I := C.val.map T.boundaryι
      let g := (T.snoc C.val C.property).boundaryι
      have heq : (I.comap I.blowupToBase).comap g = C.val :=
        T.comap_exceptional_boundaryι_snoc C.val C.property
      let hE := I.isEffectiveCartier_comap_blowupToBase
      let h := heq.symm ▸ C.property
      exact congrArg Inv.inv
        ((hE.pullback_mk_toInvertibleSheaf h).trans (mk_toInvertibleSheaf_congr _ _ heq))
    · simpa only [WithBoundary.toTower_snoc, exceptionalClass_snoc_castSucc, pullback_comp,
        WithBoundary.boundaryι_snoc_blowupToBase]
        using ih (fun k ↦ J k.castSucc) k

/-- Restriction of a marked class pulls back the original class along `i` and tensors
it with the center ideal line bundles raised to the negatives of the exceptional
coefficients. -/
theorem pullback_picardHom_alongBoundary (a : Additive (LineBundleClass X)) (b : Fin n → ℤ) :
    pullback (alongBoundary i J).2.boundaryι
        ((alongBoundary i J).2.toTower.picardHom (a, b)).toMul =
      pullback i a.toMul * ∏ j, (mk (J j).property.toInvertibleSheaf) ^ (-b j) := by
  rw [picardHom_apply_toMul, pullback_mul, pullback_comp, WithBoundary.boundaryι_toBase]
  rw [← pullbackHom_apply (f := (alongBoundary i J).2.boundaryι) (a := ∏ j : Fin n, _), map_prod]
  simp only [pullbackHom_apply, pullback_zpow, pullback_exceptionalClass_alongBoundary,
    inv_zpow, zpow_neg]

/-- For fixed Picard coordinates, the ratio of the restrictions along two towers is a
product of ratios of the original center ideal classes. -/
theorem pullback_picardHom_alongBoundary_div
    (K : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (a : Additive (LineBundleClass X)) (b : Fin n → ℤ) :
    pullback (alongBoundary i J).2.boundaryι
        ((alongBoundary i J).2.toTower.picardHom (a, b)).toMul /
      pullback (alongBoundary i K).2.boundaryι
        ((alongBoundary i K).2.toTower.picardHom (a, b)).toMul =
      ∏ j, (mk (J j).property.toInvertibleSheaf / mk (K j).property.toInvertibleSheaf) ^
        (-b j) := by
  simp only [pullback_picardHom_alongBoundary, mul_div_mul_left_eq_div, div_zpow,
    Finset.prod_div_distrib]

end QPainleve.BlowupTower
