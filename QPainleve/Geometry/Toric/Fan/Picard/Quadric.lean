/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Quadric

/-!
# Picard coordinates under the quadric ruling exchange

The ruling exchange of the Hirzebruch fan of index zero interchanges the two
integral Picard coordinates. Transport of a closed point blowup tower by this exchange
preserves its ordered exceptional coefficients.
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

namespace QPainleve.BlowupTower.IsClosedPointTower

open CategoryTheory TauCeti.Toric LineBundleClass

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "Pic" => Additive (LineBundleClass X)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "E" => Fan.quadricRulingExchange b hΦ hc r hr
local notation "τ" => FanHom.algebraicMap (FanEquiv.toFanHom (E))
local notation "Q(" T ")" => BlowupTower.transport T (asIso τ)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

/-- On transport of a closed point tower by the toric ruling exchange, the base
coordinates of a line bundle are transposed and its total exceptional coefficients
are unchanged. The transported line bundle is pulled back along the inverse lift. -/
theorem picardMarking_symm_rulingExchange (L : LineBundleClass Y) :
    let : SmoothOfRelativeDimension 2 f := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let q := Q(T)
    let hQ := q.isLift.isClosedPointTower hT
    let v : Pic × (Fin n → ℤ) := (T.picardMarking hT f).symm (Additive.ofMul L)
    let w : Pic × (Fin n → ℤ) :=
      (q.tower.picardMarking hQ f).symm (Additive.ofMul (pullback q.iso.inv L))
    (∀ j : Fin 2, (C).repr w.1 j = (C).repr v.1 (Equiv.swap 0 1 j)) ∧ w.2 = v.2 := by
  intro hSmooth q hQ v w
  let : SmoothOfRelativeDimension 2 f := hSmooth
  have hτ : (asIso τ).inv = τ := by
    apply (cancel_mono τ).mp
    exact (by simpa only [asIso_hom] using (asIso τ).inv_hom_id :
      (asIso τ).inv ≫ τ = 𝟙 X).trans (Fan.quadricRulingExchange_algebraicMap_comp ..).symm
  have hv : (T.picardHom v).toMul = L := by
    rw [← picardMarking_apply T hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hw : w = (Additive.ofMul (pullback τ v.1.toMul), v.2) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [toMul_ofMul, picardMarking_apply]
    simpa only [Iso.symm_hom, hτ, hv, Prod.mk.eta] using q.isLift.symm.pullback_picardHom v.1 v.2
  rw [hw]
  exact ⟨Fan.hirzebruchPicardBasis_repr_pullback_quadricRulingExchange b hΦ hc r hr v.1, rfl⟩

end QPainleve.BlowupTower.IsClosedPointTower
