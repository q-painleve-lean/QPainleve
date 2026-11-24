/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

/-!
# Picard coordinates under the quadric ruling exchange

The ruling exchange of the Hirzebruch fan of index zero interchanges the two
integral Picard coordinates.
-/

public noncomputable section

open AlgebraicGeometry Module
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "E" => quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))

variable [Nonempty Φ.cones]

local notation "C" => hirzebruchPicardBasis b 0 hΦ r hr

open LineBundleClass in
/-- Pullback along the ruling exchange swaps the two Hirzebruch Picard coordinates. -/
theorem hirzebruchPicardBasis_repr_pullback_quadricRulingExchange
    (L : Additive (LineBundleClass Φ.algebraicRealization)) (j : Fin 2) :
    (C).repr (Additive.ofMul (pullback τ L.toMul)) j = (C).repr L (Equiv.swap 0 1 j) := by
  let P := (pullbackHom τ).toAdditive.toIntLinearMap
  have hP (k : Fin 2) : P (C k) = C (Equiv.swap 0 1 k) := by
    have h₀ := (E).pullback_primeDivisorClass_rayBoundaryPoint hΦ hΦ (r 0)
    have h₁ := (E).pullback_primeDivisorClass_rayBoundaryPoint hΦ hΦ (r 1)
    simp only [quadricRulingExchange_rayEquiv, sub_zero, sub_self] at h₀ h₁
    fin_cases k
    · simpa [P, rayDivisorToPicard_single] using congrArg Additive.ofMul h₀
    · simpa [P, rayDivisorToPicard_single] using congrArg Additive.ofMul h₁
  have he : P = (C).equiv (C) (Equiv.swap 0 1) := by
    apply (C).ext
    intro k
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, hP]
  have hPL : P L = Additive.ofMul (pullback τ L.toMul) := by simp [P]
  rw [← hPL, he, LinearEquiv.coe_coe, Basis.equiv, LinearEquiv.trans_apply]
  let s := Equiv.swap (0 : Fin 2) 1
  have h := (C).repr_reindex_apply (e := s.symm)
    (((C).reindex s.symm).repr.symm ((C).repr L)) (s j)
  simpa only [s, Equiv.symm_symm, Equiv.swap_apply_self, LinearEquiv.apply_symm_apply] using h.symm

end TauCeti.Toric.Fan
