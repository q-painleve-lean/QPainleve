/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Quadric

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nef
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Separation of high-multiplicity centers on the quadric

The two selected centers of the quadric link must lie on distinct fibers of the
exchanged ruling. If their combined order exceeds the degree on a transverse fiber,
intersection with its strict transform on the specified resolution rules out
a common fiber. This proves the separation in Case B of Proposition 8.11 in
Lutz's appendix to [*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "m" => LinearMap.toAddMonoidHom (Basis.coord b 0)
local notation "p(" t ")" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) 0 (t : ℂ)

local notation "h" => Fan.nonneg_or_nonpos_quadric_transverse_character b r hr
local notation "f" => Φ.characterRuling m h

variable {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

local notation "P₂" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "π" => T.toBase ≫ (X ↘ S)

include hc in
/-- Two first centers of a resolved quadric-to-plane map lie on different
transverse fibers if their combined order exceeds the transverse fiber degree
and the first center lies over the base torus. -/
theorem ne_quadric_transverse_ruling_of_lt_sum_first_base_orders
    (g : Y ⟶ P₂) (hg : g ≫ (P₂ ↘ S) = π)
    {j l : Fin n} (hjl : j ≠ l)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j)
    (hl : ∀ i < l, hT.baseCenter i ≠ hT.baseCenter l)
    (t : ℂˣ) (ht : f (hT.baseCenter j) ∈ Set.range (p(t))) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let v := (T.picardMarking hT (X ↘ S)).symm (Additive.ofMul (pullback g H))
    (C).repr v.1 0 < -v.2 j + -v.2 l →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro hSmooth v hsum heq
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hSmooth
  have hmark : (T.picardHom v).toMul = pullback g H := by
    rw [← picardMarking_apply _ hT (X ↘ S), LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hample : (H).IsAmple :=
    TauCeti.SymmetricAlgebra.isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  let : Y.Over S := ⟨π⟩
  let : g.IsOver S := ⟨hg⟩
  have hnef : (T.picardHom v).toMul.IsNef ℂ π := hmark.symm ▸ hample.isNef.pullback g
  let orders (i : Fin n) := (-v.2 i).toNat
  have horders (i : Fin n) : (orders i : ℤ) = -v.2 i :=
    Int.toNat_of_nonneg (neg_nonneg.mpr (hT.exceptionalCoeff_nonpos_of_isNef_picardHom hnef i))
  have hneg : (fun i ↦ -(orders i : ℤ)) = v.2 := funext fun i ↦ by rw [horders, neg_neg]
  have hnef' : (T.picardHom (v.1, fun i ↦ -(orders i : ℤ))).toMul.IsNef ℂ π := by
    rwa [hneg, Prod.mk.eta]
  classical
  have hbound := hT.sum_first_base_orders_le_quadric_transverse_fiber_degree
    b hΦ hc r hr v.1 orders {j, l} t (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨ht, hj⟩
      · exact ⟨heq ▸ ht, hl⟩) hnef'
  rw [Finset.sum_pair hjl, horders, horders] at hbound
  exact (not_lt_of_ge hbound) hsum

end QPainleve.BlowupTower.IsClosedPointTower
