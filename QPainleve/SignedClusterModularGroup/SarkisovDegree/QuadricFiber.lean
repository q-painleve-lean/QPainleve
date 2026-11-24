/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.Geometry.Toric.Fan.Picard.Quadric

import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Separation of high-multiplicity centers on the quadric

The two selected centers of the quadric link must lie on distinct fibers of the
exchanged ruling. The two-point Sarkisov inequality makes their combined order
larger than the degree on a transverse fiber. If they shared that fiber,
intersection with its strict transform on the specified resolution would
contradict nefness. This proves the separation in Case B of Proposition 8.11 in
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

include hc in
private theorem ne_quadric_transverse_ruling_of_homaloidal
    (L : Additive (LineBundleClass X)) (orders : Fin n → ℕ) {j l : Fin n} (hjl : j ≠ l)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j)
    (hl : ∀ i < l, hT.baseCenter i ≠ hT.baseCenter l)
    (t : ℂˣ) (ht : f (hT.baseCenter j) ∈ Set.range (p(t)))
    (hnef : (T.picardHom (L, fun i ↦ -(orders i : ℤ))).toMul.IsNef ℂ (T.toBase ≫ (X ↘ S))) :
    let a := (C).repr L 0
    let β := (C).repr L 1
    (∑ i, (orders i : ℤ) ^ 2) = 2 * a * β - 1 →
    (∑ i, (orders i : ℤ)) = 2 * a + 2 * β - 3 →
    β < 2 * (orders j : ℤ) → (orders j : ℤ) ≤ β →
    β < 2 * (orders l : ℤ) → (orders l : ℤ) ≤ β →
    (∀ i, i ≠ j → i ≠ l → 2 * (orders i : ℤ) ≤ β) →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro a β hsq hsum hjbig hjle hlbig hlle hsmall heq
  classical
  have hβ : 0 < β := by omega
  have hnum := quadric_sarkisov_degree_decrease_of_pair hβ hjl hsq hsum hjbig.le hjle hlbig.le hlle
    (fun i hi hi' ↦ ⟨Nat.cast_nonneg _, hsmall i hi hi'⟩)
  have hbound := hT.sum_first_base_orders_le_quadric_transverse_fiber_degree
    b hΦ hc r hr L orders {j, l} t (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨ht, hj⟩
      · exact ⟨heq ▸ ht, hl⟩) hnef
  rw [Finset.sum_pair hjl] at hbound
  omega

local notation "P₂" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "π" => T.toBase ≫ (X ↘ S)

include hc in
/-- For a resolved quadric-to-plane map in the two-high-order case, the selected
proper centers lie on distinct fibers of the exchanged ruling if one lies over the
base torus. The orders are read from the total exceptional coordinates of the
resolved line class. Each selected order is at most the original fiber degree, and
every other order is at most half that degree. -/
theorem ne_quadric_transverse_ruling_of_two_high_base_orders
    (g : Y ⟶ P₂) (hg : g ≫ (P₂ ↘ S) = π) (hbir : Scheme.BirationalOver g (𝟙 P₂))
    {j l : Fin n} (hjl : j ≠ l)
    (hj : ∀ i < j, hT.baseCenter i ≠ hT.baseCenter j)
    (hl : ∀ i < l, hT.baseCenter i ≠ hT.baseCenter l)
    (t : ℂˣ) (ht : f (hT.baseCenter j) ∈ Set.range (p(t))) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let v := (T.picardMarking hT (X ↘ S)).symm (Additive.ofMul (pullback g H))
    let β := (C).repr v.1 1
    (∀ i, 0 ≤ -v.2 i) →
    β < 2 * (-v.2 j) → -v.2 j ≤ β →
    β < 2 * (-v.2 l) → -v.2 l ≤ β →
    (∀ i, i ≠ j → i ≠ l → 2 * (-v.2 i) ≤ β) →
    f (hT.baseCenter j) ≠ f (hT.baseCenter l) := by
  intro hSmooth v β hn hjbig hjle hlbig hlle hsmall
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hSmooth
  let orders (i : Fin n) := (-v.2 i).toNat
  have horders (i : Fin n) : (orders i : ℤ) = -v.2 i := Int.toNat_of_nonneg (hn i)
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hmark := congrArg Additive.toMul ((T.picardMarking hT (X ↘ S)).apply_symm_apply
    (Additive.ofMul (pullback g H)))
  rw [T.picardMarking_apply, toMul_ofMul] at hmark
  have hneg : (fun i ↦ -(orders i : ℤ)) = v.2 := funext fun i ↦ by rw [horders, neg_neg]
  have hample : (H).IsAmple :=
    TauCeti.SymmetricAlgebra.isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  let : Y.Over S := ⟨π⟩
  have : g.IsOver S := ⟨hg⟩
  have hnef : (T.picardHom (v.1, fun i ↦ -(orders i : ℤ))).toMul.IsNef ℂ π := by
    rw [hneg, Prod.mk.eta, hmark]
    exact hample.isNef.pullback g
  refine ne_quadric_transverse_ruling_of_homaloidal b hΦ hc r hr hT v.1 orders hjl hj hl t ht hnef
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [horders, neg_sq, Nat.cast_zero, zero_mul, sub_zero] using hsq
  · simpa only [horders, Nat.cast_zero, sub_zero] using hsum
  · simpa only [horders] using hjbig
  · simpa only [horders] using hjle
  · simpa only [horders] using hlbig
  · simpa only [horders] using hlle
  · simpa only [horders] using hsmall

end QPainleve.BlowupTower.IsClosedPointTower
