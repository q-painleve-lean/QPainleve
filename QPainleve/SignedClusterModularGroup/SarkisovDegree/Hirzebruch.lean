/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nef
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Multiplicity
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# High multiplicities on Hirzebruch resolutions

On a specified resolution of a birational map from a Hirzebruch surface to the
plane, the pullback of the line class is nef. Its base coordinates give a positive
fiber degree and nonnegative degree on the section of square `-e`. The homaloidal
identities then force a base order greater than half the fiber degree, except
in the cases of the quadric and the first Hirzebruch surface where ruling exchange
and section contraction apply.

This is the Hirzebruch case of Lemma 8.8 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Φ.algebraicRealization.IsProjectiveOver ℂ]
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
private theorem hirzebruch_basis_intersections [Nonempty Φ.cones]
    [SmoothOfRelativeDimension 2 f] (x : Additive (LineBundleClass X)) :
    B x (C 0) = (C).repr x 1 ∧ B x (C 1) = (C).repr x 0 - (e : ℤ) * (C).repr x 1 := by
  let a := (C).repr x 0
  let d := (C).repr x 1
  have hx : x = a • C 0 + d • C 1 := by
    simpa only [a, d, Fin.sum_univ_two] using ((C).sum_repr x).symm
  have h (j : Fin 2) : B x (C j) =
      a * (!![0, 1; 1, -(e : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 0 j +
        d * (!![0, 1; 1, -(e : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
    conv_lhs => rw [hx]
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Int.zsmul_eq_mul,
      Fan.hirzebruchPicardBasis_intersection b e hΦ r hr hc]
  exact ⟨by simpa using h 0, by simpa [sub_eq_add_neg, mul_comm d] using h 1⟩

variable {Y : Scheme.{0}} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}

/-- The resolved line class of a birational map to the plane has positive fiber
degree and nonnegative intersection with the section of square `-e`. The negatives of
its exceptional coefficients, including those at infinitely near points, are
nonnegative. -/
theorem hirzebruch_resolution_degree_bounds (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking (k := ℂ) hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr v.1 0
    let d := (C).repr v.1 1
    0 < d ∧ (e : ℤ) * d ≤ a ∧ ∀ j, 0 ≤ -v.2 j := by
  classical
  intro hcones hdim hnoeth v a d
  let := hcones
  let := hdim
  let := hnoeth
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : g.IsOver S := ⟨hg⟩
  have hH : (H).IsAmple := isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  have hv : (T.picardHom v).toMul = pullback g H := by
    rw [← picardMarking_apply _ hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hnef : (T.picardHom v).toMul.IsNef ℂ (T.toBase ≫ f) :=
    hv.symm ▸ hH.isNef.pullback g
  have hbase := hT.isNef_fst_of_isNef_picardHom hnef
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  have := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  have hnonneg := (isNef_iff_classIntersectionNumber_nonneg ℂ hX _).mp hbase
  have hF : 0 ≤ B v.1 (C 0) := by
    simpa only [Fan.hirzebruchPicardBasis_apply_zero, Fan.rayDivisorToPicard_single,
      one_zsmul, intersectionBilinForm_apply, toMul_ofMul] using
      hnonneg (Φ.rayBoundaryPoint hΦ (r 1))
  have hB : 0 ≤ B v.1 (C 1) := by
    simpa only [Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single,
      one_zsmul, intersectionBilinForm_apply, toMul_ofMul] using
      hnonneg (Φ.rayBoundaryPoint hΦ (r 0))
  obtain ⟨hd, ha⟩ := hirzebruch_basis_intersections b e hΦ hc r hr v.1
  rw [hd] at hF
  rw [ha] at hB
  have hd₀ : d ≠ 0 := by
    intro hzero
    have hsq : (∑ j, (v.2 j) ^ 2) = 2 * a * d - (e : ℤ) * d ^ 2 - 1 :=
      (hT.homaloidal_intersection_identities_of_hirzebruch b e hΦ hc r hr g hg hbir).1
    simp only [hzero, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_sub] at hsq
    have hsum : 0 ≤ ∑ j, (v.2 j) ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg (v.2 j)
    omega
  exact ⟨lt_of_le_of_ne hF (Ne.symm hd₀), sub_nonneg.mp hB,
    fun j ↦ neg_nonneg.mpr (hT.exceptionalCoeff_nonpos_of_isNef_picardHom hnef j)⟩

/-- Every specified Hirzebruch resolution of a birational map to the plane either
has a base order greater than half the fiber degree or falls into one of the two
lower-index cases. With all orders at most half the fiber degree, the quadric
has smaller degree after exchange of rulings, and on the first Hirzebruch surface
the plane degree after section contraction is less than three halves of the
original fiber degree. -/
theorem exists_fiber_degree_lt_two_mul_or_of_hirzebruch_resolution
    (hT : IsClosedPointTower X T) (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      (by simpa using Module.finrank_eq_card_basis b : Module.finrank ℤ N = 2) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking (k := ℂ) hT f).symm (Additive.ofMul (pullback g H))
    let a := (C).repr v.1 0
    let d := (C).repr v.1 1
    (∃ j, d < 2 * (-v.2 j)) ∨
      ((∀ j, 2 * (-v.2 j) ≤ d) ∧ (e = 0 ∧ a < d ∨ e = 1 ∧ 2 * a < 3 * d)) := by
  intro hcones hdim hnoeth v a d
  let := hcones
  let := hdim
  let := hnoeth
  by_cases hhigh : ∃ j, d < 2 * (-v.2 j)
  · exact Or.inl hhigh
  push Not at hhigh
  refine Or.inr ⟨hhigh, ?_⟩
  obtain ⟨hd, ha, hm⟩ := hirzebruch_resolution_degree_bounds b e hΦ hc r hr hT g hg hbir
  obtain ⟨hsq, hsum⟩ :=
    hT.homaloidal_intersection_identities_of_hirzebruch b e hΦ hc r hr g hg hbir
  have h := exists_fiber_degree_lt_two_mul_or_of_hirzebruch_homaloidal (Int.natCast_nonneg e)
    hd ha hm (by simpa only [neg_sq] using hsq) hsum
  rcases h with ⟨j, hj⟩ | ⟨he, hlt⟩ | ⟨he, hlt⟩
  · exact (not_lt_of_ge (hhigh j) hj).elim
  · exact Or.inl ⟨by exact_mod_cast he, hlt⟩
  · exact Or.inr ⟨by exact_mod_cast he, hlt⟩

end QPainleve.BlowupTower.IsClosedPointTower
