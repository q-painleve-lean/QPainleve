/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SmoothSection

import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Hirzebruch
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease

/-!
# The one-point Sarkisov block from the quadric

For one high-order base point in the interior of a toric fiber of a quadric,
read the quadric marking with its two rulings exchanged. The center is now
on a section. Mutate to the first Hirzebruch surface and contract its negative
section. Both links carry the same specified resolution, and the homaloidal
identities imply that the final plane degree divided by three is strictly
less than the original fiber degree divided by two.

This is Case A of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "v" => Fan.Ray.primitiveGenerator (r 0)
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero (r 0)
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem (r 0)

local notation "hop" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch b 0 r hr
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp hop) hc
local notation "s" => r.trans (Φ.mutationFanRayEquiv b hv hp hop)
local notation "hs" => Fan.Ray.mutationFan_hirzebruch_ray_generators_of_section_zero
  (r 0) b hop 0 r hr rfl
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "fP" => (P ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "C'" => Fan.hirzebruchPicardBasis b 1 hΨ s hs
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pivotPoint[" c "]" =>
  (Fan.Ray.binomialCenter (r 0) rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter (r 0) b) c) (IsLocalRing.closedPoint ℂ)
local notation "mutationMap[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp hop)
local notation "sourceCenter[" c "]" => Fan.Ray.mutationSourceCenterIdeal b (r 0) c
local notation "targetCenter[" c "]" => Fan.Ray.mutationTargetCenterIdeal b (r 0) hop c
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ r 0) () hop ()
local notation "reversePoint[" c "]" =>
  (Fan.Ray.binomialCenter (reverseRay) rankTwo
    (b.detDualEquiv_self (Fan.Ray.primitiveGenerator (reverseRay)))
    (Fan.Ray.surjective_detCharacter (reverseRay) b) c⁻¹) (IsLocalRing.closedPoint ℂ)

variable {n : ℕ} {Y : Scheme.{0}} {T : BlowupTower Φ.algebraicRealization (n + 1) Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)

local notation "firstIndex" => Fin.castAdd n (0 : Fin 1)

/-- Mutating a complete regular quadric at the first blowup over the chosen binomial
section point carries a specified plane resolution to the Hirzebruch-one fan.
The isomorphism of resolving surfaces gives the mutation square. In the two
Picard markings, the old base coordinates `(b, a)` become `(b + a - m, a)`,
where `m` is the order at the pivot. The first new order is `a - m` and the
other orders keep their original relative order. The first new center is the
reverse pivot, and the remaining projected centers correspond through the
common pivot blowup, including for infinitely near centers. -/
theorem exists_hirzebruchOne_resolution_of_quadric_mutation
    (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c : ℂˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivotPoint[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivotPoint[c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : SmoothOfRelativeDimension 2 fX' := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X := by
      let : Smooth Φ.algebraicRealizationStructureMap :=
        Φ.smooth_algebraicRealizationStructureMap hΦ
      exact isNoetherian_of_finiteType Φ.algebraicRealizationStructureMap
    let : IsNoetherian X' := by
      let : Smooth (Ψ).algebraicRealizationStructureMap :=
        (Ψ).smooth_algebraicRealizationStructureMap hΨ
      exact isNoetherian_of_finiteType (Ψ).algebraicRealizationStructureMap
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    ∃ (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (hU : IsClosedPointTower X' U) (e : Y ≅ Z),
      T.toBase.toRationalMap.comp mutationMap[c] = (e.hom ≫ U.toBase).toRationalMap ∧
      (e.inv ≫ g) ≫ fP = U.toBase ≫ fX' ∧
      Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
      hU.baseCenter firstIndex = reversePoint[c] ∧
      (∀ l : Fin n, ∃ p : (sourceCenter[c]).blowup,
        (sourceCenter[c]).blowupToBase p = hT.baseCenter (j.succAbove l) ∧
        (targetCenter[c]).blowupToBase (((r 0).mutationBlowupIso b hop c).hom p) =
          hU.baseCenter (l.natAdd 1)) ∧
      let y := (U.picardMarking hU fX').symm (Additive.ofMul (pullback (e.inv ≫ g) H))
      (C').repr y.1 0 = (C).repr x.1 0 + (C).repr x.1 1 + x.2 j ∧
      (C').repr y.1 1 = (C).repr x.1 1 ∧
      y.2 firstIndex = -(C).repr x.1 1 - x.2 j ∧
      ∀ l : Fin n, y.2 (l.natAdd 1) = x.2 (j.succAbove l) := by
  intro hcones hcones' hdim hdim' hnoeth hnoeth' hY hmod x
  let := hcones
  let := hcones'
  let := hdim
  let := hdim'
  let := hnoeth
  let := hnoeth'
  let := hY
  let := hmod
  obtain ⟨Z, U, e, hU, hover, hmap, hreverse, hcenters, hcoords⟩ :=
    Fan.Ray.exists_sarkisov_decrease_of_smooth_section_center (r 0) b hop c hΦ hT j hj hfirst
  have hg' : (e.inv ≫ g) ≫ fP = U.toBase ≫ fX' := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc e.hom, Iso.hom_inv_id_assoc, hg, ← hover]
  have hb' : Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) := by
    refine Scheme.BirationalOver.trans (sY := g) ⟨.ofIso e.symm, ?_⟩ hbir
    simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]
  refine ⟨Z, U, hU, e, hmap, hg', hb', hreverse, hcenters, ?_⟩
  intro y
  let a := (C).repr x.1 0
  let d := (C).repr x.1 1
  let orders := (Fin.addCases (fun _ : Fin 1 ↦ x.2 j) (x.2 ∘ j.succAbove) : Fin (1 + n) → ℤ)
  let w := Function.update orders firstIndex (-d - x.2 j)
  have hx : x.1 = a • C 0 + d • C 1 := by
    simpa only [a, d, Fin.sum_univ_two] using ((C).sum_repr x.1).symm
  have hxH : (T.picardHom x).toMul = pullback g H := by
    rw [← picardMarking_apply T hT fX, LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hw : y = ((a + x.2 j + d) • C' 0 + d • C' 1, w) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [picardMarking_apply, toMul_ofMul, ← pullback_comp, ← hxH]
    have h := (hcoords true a d x.2).1
    have hF' := Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero b 1 hΨ s hs
    simp only [Equiv.trans_apply] at hF'
    simp only [↓reduceIte, Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero b 0 hΦ r hr,
      hF', Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_zsmul] at hx h
    rw [← hx, Prod.mk.eta] at h
    simpa only [Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_zsmul,
      Equiv.trans_apply] using h
  rw [hw]
  have hrepr := (C').equivFun.apply_symm_apply (![a + x.2 j + d, d] : Fin 2 → ℤ)
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, Basis.equivFun_apply] at hrepr
  refine ⟨(congrFun hrepr 0).trans (add_right_comm _ _ _), congrFun hrepr 1, ?_, ?_⟩
  · simp only [w, d, Function.update_self]
  · intro l
    have hne : l.natAdd 1 ≠ firstIndex := by
      rw [← Fin.val_ne_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero]
      omega
    simp only [w, orders, Function.update_of_ne hne, Fin.addCases_right, Function.comp_apply]

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

/-- The one-point block from a quadric carries a specified plane resolution
across the mutation and the subsequent toric contraction to the plane.
The quadric is written in the frame of the exchanged ruling, so its original
fiber degree is the coefficient of the fiber in the displayed frame. The
selected pivot lies on the chosen section in this frame.

If the pivot is the only order greater than half the original fiber degree,
and is bounded by that fiber degree, the plane degree is positive and its
Sarkisov bidegree is strictly smaller. The two new exceptional coordinates
are those of the contracted section and the reverse pivot. Every other
coordinate retains its original relative order. -/
theorem exists_plane_resolution_of_quadric_single_high_center
    (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c : ℂˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivotPoint[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivotPoint[c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := by
      let : Smooth Φ.algebraicRealizationStructureMap :=
        Φ.smooth_algebraicRealizationStructureMap hΦ
      exact isNoetherian_of_finiteType Φ.algebraicRealizationStructureMap
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let b₀ := (C).repr x.1 0
    let a₀ := (C).repr x.1 1
    let m := fun l ↦ -x.2 l
    0 < b₀ → b₀ < 2 * m j → m j ≤ b₀ →
      (∀ l ≠ j, 0 ≤ m l ∧ 2 * m l ≤ b₀) →
      ∃ (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (_ : IsClosedPointTower X' U)
        (e : Y ≅ Z) (d : Basis (Fin 2) ℤ N)
        (s₀ : (Ψ).IsSubdivision (Fan.projectiveSpace d (Ψ).lattice))
        (W : Scheme) (V₀ : BlowupTower P (1 + (1 + n)) W) (hV : IsClosedPointTower P V₀)
        (k : Z ≅ W),
        T.toBase.toRationalMap.comp mutationMap[c] = (e.hom ≫ U.toBase).toRationalMap ∧
        k.hom ≫ V₀.toBase = U.toBase ≫ s₀.toFanHom.algebraicMap ≫
          (Fan.projectivePlaneIso d (Ψ).lattice).hom ≫
          (Pi.basisFun ℂ (Fin 3)).polynomialProjIso.hom ∧
        (k.inv ≫ e.inv ≫ g) ≫ fP = V₀.toBase ≫ fP ∧
        Scheme.BirationalOver (k.inv ≫ e.inv ≫ g) (𝟙 P) ∧
        let y := (V₀.picardMarking hV fP).symm (Additive.ofMul (pullback (k.inv ≫ e.inv ≫ g) H))
        degree y.1 = b₀ + a₀ - m j ∧
        y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = m j - b₀ ∧
        y.2 (Fin.natAdd 1 firstIndex) = m j - a₀ ∧
        (∀ l : Fin n, y.2 (Fin.natAdd 1 (l.natAdd 1)) = x.2 (j.succAbove l)) ∧
        0 < degree y.1 ∧
        planeSarkisovBidegree (degree y.1).toNat (∑ l, -y.2 l).toNat <
          hirzebruchSarkisovBidegree b₀.toNat (∑ l, m l).toNat := by
  intro hcones hcones' hdim hnoeth hY hmod x b₀ a₀ m hb hm hmb hsmall
  let := hcones
  let := hcones'
  let := hdim
  let := hnoeth
  let := hY
  let := hmod
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hlt := quadric_sarkisov_degree_decrease_of_single (a := a₀) (m := m) hb j
    (by
      have hmul : 2 * a₀ * b₀ = 2 * b₀ * a₀ := mul_right_comm 2 a₀ b₀
      simpa only [m, neg_sq, Nat.cast_zero, zero_mul, sub_zero, hmul] using hsq)
    (by
      have hadd : 2 * a₀ + 2 * b₀ = 2 * b₀ + 2 * a₀ := add_comm _ _
      simpa only [m, Nat.cast_zero, sub_zero, hadd] using hsum)
    hm.le hmb hsmall
  obtain ⟨Z, U, hU, e, hmap, hg', hbir', _, _, hα, hβ, hfirst', htail⟩ :=
    hT.exists_hirzebruchOne_resolution_of_quadric_mutation b hΦ hc r hr g hg hbir c j hj hfirst
  obtain ⟨d, s₀, W, V₀, hV, k, hproj, hg'', hbir'', hdegree, hvertex, hrem, -⟩ :=
    hU.exists_plane_resolution_of_hirzebruchOne b hΨ hcΨ s hs (e.inv ≫ g) hg' hbir'
  refine ⟨Z, U, hU, e, d, s₀, W, V₀, hV, k, hmap, hproj,
    by simpa only [Category.assoc] using hg'', by simpa only [Category.assoc] using hbir'', ?_⟩
  intro y
  have hy : degree y.1 = b₀ + a₀ - m j := by
    simpa only [y, Category.assoc, hα, b₀, a₀, m, sub_neg_eq_add] using hdegree
  have hf : y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = m j - b₀ := by
    have h : y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = a₀ - (b₀ + a₀ - m j) := by
      simpa only [y, Category.assoc, hβ, hα, b₀, a₀, m, sub_neg_eq_add] using hvertex
    omega
  refine ⟨hy, hf, ?_, ?_, hy ▸ hlt.1, ?_⟩
  · have h : y.2 (Fin.natAdd 1 firstIndex) = -a₀ - x.2 j := by
      simpa only [y, Category.assoc, hfirst', a₀] using hrem firstIndex
    dsimp only [m]
    omega
  · intro l
    simpa only [y, Category.assoc, htail] using hrem (l.natAdd 1)
  · rw [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    refine Or.inl ?_
    rw [hy]
    omega

end QPainleve.BlowupTower.IsClosedPointTower
