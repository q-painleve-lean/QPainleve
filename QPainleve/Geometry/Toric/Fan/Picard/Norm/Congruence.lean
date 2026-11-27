/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Norm.Formula

import Mathlib.Algebra.BigOperators.ModEq
import QPainleve.Geometry.Toric.Fan.CyclicOrder.Basic
import QPainleve.Geometry.Toric.BaseChange.Fan

/-!
# The norm congruence for toric blowup markings

The square of a boundary-orthogonal class is congruent to the negative sum of
the squares of its exceptional coordinates modulo any common divisor of the
charge determinants. Each term of the clockwise sum contains one of these determinants.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Chow
open LinearMap (BilinForm)

namespace TauCeti.Toric.Fan

variable (k : Type) [Field k] [Infinite k]

variable {N : Type} {V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [Nonempty Φ.cones] [(Φ.finiteFanScheme k).IsProjectiveOver k]
  (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "X" => (Φ.finiteFanScheme k)
local notation "gen" => Ray.primitiveGenerator (Phi := Φ)
local notation "det" => b.detDualEquiv

variable [Fintype ι]

local notation "B" => intersectionBilinForm k X
local notation "Q" => BilinForm.prod B (-(dotProductBilin ℤ ℤ : BilinForm ℤ (ι → ℤ)))

include hc

local notation "Surface" =>
  SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k) ↘ Spec (CommRingCat.of k))

/-- The norm of a boundary-orthogonal class in an ordered internal blowup marking is
congruent to the negative sum of the squares of its exceptional coordinates modulo any
common divisor of the pairwise charge determinants. The result allows repeated rays
and charge images of any rank. -/
theorem boundaryOrthogonal_norm_modEq (s : ι → Φ.Ray) :
    let _ : Surface := by
      rw [Φ.finiteFanScheme_over k]
      have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      exact hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
    ∀ (y : BilinForm.orthogonal Q (LinearMap.range (markedBoundaryMap k hΦ s)))
      {d : ℤ}, (∀ j k, d ∣ det (gen (s j)) (gen (s k))) →
        (Q) y.val y.val ≡ -∑ j, (y.val.2 j) ^ 2 [ZMOD d] := by
  intro _ y d hd
  have : Nontrivial N := b.equivFun.toEquiv.nontrivial
  have : Nonempty Φ.Ray := Φ.nonempty_ray_of_isComplete hc
  have : NeZero (Nat.card Φ.Ray) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨u, -, hu⟩ := (existsUnique_cyclicRayNumbering b hΦ hc (Classical.arbitrary Φ.Ray)).exists
  rw [boundary_orthogonal_norm_eq_sum_det k b hΦ hc u hu s y]
  apply Int.modEq_iff_dvd.mpr
  rw [sub_sub_cancel]
  exact Finset.dvd_sum fun k _ ↦ Finset.dvd_sum fun l _ ↦
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hd k l) _) _

/-- In charge-kernel coordinates the square of a boundary-orthogonal class is congruent to
the negative sum of squares of the relation coefficients modulo any common divisor of
the pairwise charge determinants. -/
theorem boundaryOrthogonalEquivChargeKernel_symm_norm_modEq (s : ι → Φ.Ray) :
    let _ : Surface := by
      rw [Φ.finiteFanScheme_over k]
      have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      exact hN ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
    ∀ [LinearMap.IsPerfPair Q] (x : (rayChargeMap s).ker) {d : ℤ},
      (∀ j k, d ∣ det (gen (s j)) (gen (s k))) →
        let y := (boundaryOrthogonalEquivChargeKernel k hΦ s Q).symm x
        (Q) y.val y.val ≡ -∑ j, x.val j ^ 2 [ZMOD d] := by
  intro _ _ x d hd
  simpa only [boundaryOrthogonalEquivChargeKernel_symm_snd, Pi.neg_apply, neg_sq] using
    boundaryOrthogonal_norm_modEq k b hΦ hc s
      ((boundaryOrthogonalEquivChargeKernel k hΦ s Q).symm x) hd

end TauCeti.Toric.Fan
