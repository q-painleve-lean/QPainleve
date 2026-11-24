/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Homaloidal
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch

import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Homaloidal identities in Hirzebruch coordinates

The ordered blowup marking for a resolved map to the plane gives the two
homaloidal identities in the fiber and section coordinates on the source.
These are the identities used in Lutz's appendix to Hacking and Keating,
[*Homological mirror symmetry for log Calabi–Yau surfaces*, Lemmas 8.8 and 8.12](
https://arxiv.org/abs/2005.05010v3).
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "B" => intersectionBilinForm ℂ X

include hc in
/-- On a point-blowup resolution from the Hirzebruch fan of index `e` to the plane,
the line class with base coordinates `(a, d)` has exceptional coordinates
whose squares sum to `2*a*d - e*d^2 - 1` and whose negatives sum to
`2*a + (2-e)*d - 3`. The exceptional basis uses total transforms. -/
theorem homaloidal_intersection_identities_of_hirzebruch {Y : Scheme} {n : ℕ}
    {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : SmoothOfRelativeDimension 2 f :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr v.1 0
    let d := (C).repr v.1 1
    (∑ j, (v.2 j) ^ 2) = 2 * a * d - (e : ℤ) * d ^ 2 - 1 ∧
      (∑ j, -v.2 j) = 2 * a + (2 - (e : ℤ)) * d - 3 := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let : SmoothOfRelativeDimension 2 f :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian X := isNoetherian_of_finiteType f
  let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
  let a := (C).repr v.1 0
  let d := (C).repr v.1 1
  let K := Additive.ofMul (mk (canonicalBundle ℂ X 2))
  have hv : v.1 = a • C 0 + d • C 1 := by
    simpa only [a, d, Fin.sum_univ_two] using ((C).sum_repr v.1).symm
  have hsq : B v.1 v.1 = 2 * a * d - (e : ℤ) * d ^ 2 := by
    rw [hv]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
      Int.zsmul_eq_mul, Fan.hirzebruchPicardBasis_intersection b e hΦ r hr hc]
    norm_num
    ring
  have hK : B v.1 K = -(2 * a + (2 - (e : ℤ)) * d) := by
    rw [hv]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
      Int.zsmul_eq_mul, K, Fan.hirzebruchPicardBasis_intersection_canonical b e hΦ r hr hc]
    norm_num
    ring
  have h := hT.homaloidal_intersection_identities g hg hbir
  dsimp only at h
  rw [intersectionBilinForm_apply] at hsq
  simp only [intersectionBilinForm_apply, K, toMul_ofMul] at hK
  rw [hsq, hK, neg_neg] at h
  exact h

end QPainleve.BlowupTower.IsClosedPointTower
