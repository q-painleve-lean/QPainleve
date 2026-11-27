/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SmoothSection

import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Hirzebruch

/-!
# Mutation of a specified quadric resolution

With the two rulings exchanged, a smooth point on a toric fiber is on a
section. Mutation at the first blowup over this point carries a specified
plane resolution to the first Hirzebruch surface. The new Picard marking
records the reverse pivot and the order of the remaining exceptional classes.

This is Case A of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

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
local notation "S" => Spec (CommRingCat.of k₀)
local notation "P" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "X" => (Φ.finiteFanScheme k₀)
local notation "X'" => Fan.finiteFanScheme k₀ Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "fP" => (P ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis k₀ b 0 hΦ r hr
local notation "C'" => Fan.hirzebruchPicardBasis k₀ b 1 hΨ s hs
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pivotPoint[" c "]" =>
  (Fan.Ray.binomialCenter (r 0) k₀ rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter (r 0) b) c) (IsLocalRing.closedPoint k₀)
local notation "mutationMap[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap k₀ b (c : k₀) hv hp hop)
local notation "sourceCenter[" c "]" => Fan.Ray.mutationSourceCenterIdeal b (r 0) c
local notation "targetCenter[" c "]" => Fan.Ray.mutationTargetCenterIdeal b (r 0) hop c
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ r 0) () hop ()
local notation "reversePoint[" c "]" =>
  (Fan.Ray.binomialCenter (reverseRay) k₀ rankTwo
    (b.detDualEquiv_self (Fan.Ray.primitiveGenerator (reverseRay)))
    (Fan.Ray.surjective_detCharacter (reverseRay) b) c⁻¹) (IsLocalRing.closedPoint k₀)

variable {n : ℕ} {Y : Scheme.{0}} {T : BlowupTower (Φ.finiteFanScheme k₀) (n + 1) Y}
  (hT : IsClosedPointTower (Φ.finiteFanScheme k₀) T) (g : Y ⟶ (Proj (homogeneousSubmodule k₀
    (Fin 3 → k₀))))

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
    (c : k₀ˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivotPoint[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivotPoint[c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : SmoothOfRelativeDimension 2 fX' := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
    let : IsNoetherian X := by
      let : Smooth (Φ.finiteFanSchemeToSpec k₀) :=
        Φ.smooth_finiteFanSchemeToSpec k₀ hΦ
      exact isNoetherian_of_finiteType (Φ.finiteFanSchemeToSpec k₀)
    let : IsNoetherian X' := by
      let : Smooth (Fan.finiteFanSchemeToSpec k₀ (Ψ)) :=
        (Ψ).smooth_finiteFanSchemeToSpec k₀ hΨ
      exact isNoetherian_of_finiteType (Fan.finiteFanSchemeToSpec k₀ (Ψ))
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
  obtain ⟨Z, U, e, hU, hover, hmap, hreverse, hcenters, -, hcoords⟩ :=
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
    have hF' := Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero k₀ b 1 hΨ s hs
    simp only [Equiv.trans_apply] at hF'
    simp only [↓reduceIte, Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero k₀ b 0 hΦ r hr,
      hF', Fan.hirzebruchPicardBasis_apply_one, Fan.rayChartDivisorToPicard_single,
        one_zsmul] at hx h
    rw [← hx, Prod.mk.eta] at h
    simpa only [Fan.hirzebruchPicardBasis_apply_one, Fan.rayChartDivisorToPicard_single, one_zsmul,
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

end QPainleve.BlowupTower.IsClosedPointTower
