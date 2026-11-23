/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Comparing effective Cartier ideals in codimension one

Containment of effective Cartier ideals on a normal integral scheme is equivalent
to the reverse inequality of their Weil divisors. In particular, a modification
reflects containment of such ideals, since it is an isomorphism at the target's
codimension-one points.
-/

public section

open CategoryTheory Order TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme (CartierDivisor)

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {X Y : Scheme.{u}} [IsIntegral Y] {I J : Y.IdealSheafData}

/-- Inclusion of effective Cartier ideals means that the difference of their divisors
in the reverse order is effective. -/
theorem le_iff_isEffective_sub (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    I ≤ J ↔ (hI.toCartierDivisor - hJ.toCartierDivisor).IsEffective := by
  constructor
  · intro h
    obtain ⟨C, hC, hfact⟩ := (hI.le_iff_exists_eq_mul hJ.locallyPrincipal).mp h
    have hdiv := ((hI.toCartierDivisor_eq_iff (TauCeti.isEffectiveCartier_mul hC hJ)).mpr
      hfact).trans (toCartierDivisor_mul hC hJ)
    rw [hdiv, add_sub_cancel_right]
    exact hC.isEffective_toCartierDivisor
  · intro h
    let hC := h.isEffectiveCartier_idealSheaf
    have hmul := TauCeti.isEffectiveCartier_mul hC hJ
    have hfact := (hI.toCartierDivisor_eq_iff hmul).mp (by
      rw [toCartierDivisor_mul hC hJ, h.toCartierDivisor_idealSheaf]
      exact (sub_add_cancel _ _).symm)
    exact (hI.le_iff_exists_eq_mul hJ.locallyPrincipal).mpr ⟨_, hC, hfact⟩

variable [IsNoetherian Y] [IsNormalScheme Y]

/-- The Weil divisor of the smaller effective Cartier ideal has larger coefficients. -/
theorem le_iff_toWeilDivisor_le (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    I ≤ J ↔ hJ.toCartierDivisor.toWeilDivisor ≤ hI.toCartierDivisor.toWeilDivisor := by
  rw [hI.le_iff_isEffective_sub hJ, CartierDivisor.isEffective_iff_toWeilDivisor_nonneg]
  simp only [← CartierDivisor.toWeilDivisorHom_apply, map_sub, sub_nonneg]

/-- Extending effective Cartier ideals along a modification preserves and reflects
inclusion. The source only needs to be reduced. -/
theorem comap_le_comap_iff_of_isModification [IsReduced X] (f : X ⟶ Y)
    [IsModification f] (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    I.comap f ≤ J.comap f ↔ I ≤ J := by
  refine ⟨fun h ↦ (hI.le_iff_toWeilDivisor_le hJ).mpr ?_, fun h ↦ comap_mono f h⟩
  intro y
  have hy := f.mem_isoLocus_of_coheight_eq_one y.property
  obtain ⟨x, hx⟩ := f.surjective (y : Y)
  have : IsIso (f.stalkMap x) := f.isIso_stalkMap_of_mem_isoLocus (hx ▸ hy)
  have hord := stalkOrder_anti h x
  rw [I.stalkOrder_comap_of_isIso_stalkMap, J.stalkOrder_comap_of_isIso_stalkMap, hx] at hord
  have := IsNormalScheme.isDiscreteValuationRing_stalk (y : Y) y.property
  rw [← WeilDivisor.coeff, ← WeilDivisor.coeff,
    hI.coeff_toWeilDivisor_eq_stalkOrder, hJ.coeff_toWeilDivisor_eq_stalkOrder]
  have hfin : I.stalkOrder (y : Y) ≠ ⊤ := by
    rw [I.stalkOrder_def, ne_eq, Ideal.localOrder_eq_top_iff_eq_bot]
    exact hI.stalkIdeal_ne_bot _
  exact_mod_cast ENat.toNat_le_toNat hord hfin

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
