/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Reorder
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.Geometry.Toric.Fan.Mutation.Resolution
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Geometric
public import QPainleve.Geometry.Toric.Fan.Smooth
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Mutation.SectionIncidence
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Sarkisov degree at a smooth point of a ruling section

Mutation at a smooth boundary point of a ruling section identifies the two
pivot blowups. Transport through this isomorphism keeps the later blowup
centers in order and gives the change of ruling and exceptional coefficients.
A high-order center gives strict lexicographic decrease at fixed fiber degree.

This is the mutation case of Lemma 8.9 and Proposition 8.11 in
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.Toric
open QPainleve QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (ρ : Φ.Ray) (b : Basis (Fin 2) ℤ N)
  (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)
  (hΦ : Φ.IsRegular)

local notation "v" => Ray.primitiveGenerator ρ
local notation "hv" => Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Φ.mutationFan b hv hp hOpp
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hOpp) hΦ
local notation "r" => Φ.mutationFanRayEquiv b hv hp hOpp
local notation "I₀" => ρ.mutationSourceCenterIdeal b c
local notation "I₁" => ρ.mutationTargetCenterIdeal b hOpp c
local notation "E" => ρ.mutationBlowupIso b hOpp c
local notation "q" => Ray.ofPrimitiveGenerator ρ.isPrimitiveGenerator.isPrimitive.neg hOpp
local notation "P(" I ")" => BlowupTower.snoc BlowupTower.nil I
local notation "F" => mutationFiberClass b ρ hΦ
local notation "F'" => mutationFiberClass b (r ρ) hΨ

variable {n : ℕ}

local notation "k" => Fin.castAdd n (0 : Fin 1)

section Resolution

open Scheme.IdealSheafData

local notation "B" => Spec (CommRingCat.of ℂ)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" =>
  Ray.binomialCenter ρ rankTwo (b.detDualEquiv_self v) (Ray.surjective_detCharacter ρ b) c
local notation "reverseRay" => Φ.mutationFanCenterRays b (fun _ : Unit ↦ ρ) () hOpp ()
local notation "reverseCenter" =>
  Ray.binomialCenter (reverseRay) rankTwo
    (b.detDualEquiv_self (Ray.primitiveGenerator (reverseRay)))
    (Ray.surjective_detCharacter (reverseRay) b) c⁻¹
local notation "μ" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp hOpp)
local notation "reorder(" j "," x ")" =>
  (Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ Fin.succAbove j) : Fin (1 + n) → ℤ)
local notation "sectionCenters(" h "," hreg "," τ ")" =>
  IsClosedPointTower.strictTransformCenterIndices h (Fan.rayBoundaryIdeal _ hreg τ)

private theorem isClosed_mutationSourcePoint :
    IsClosed ({center (IsLocalRing.closedPoint ℂ)} : Set X) :=
  isClosed_singleton_of_section
    (ρ.binomialCenter_comp_structureMap rankTwo (b.detDualEquiv_self v)
      (ρ.surjective_detCharacter b) c)

private theorem isClosed_reverseCenter :
    IsClosed ({reverseCenter (IsLocalRing.closedPoint ℂ)} : Set X') :=
  isClosed_singleton_of_section ((reverseRay).binomialCenter_comp_structureMap rankTwo
    (b.detDualEquiv_self (reverseRay).primitiveGenerator) ((reverseRay).surjective_detCharacter b)
    c⁻¹)

private theorem mutationTargetCenterIdeal_eq_residueFieldKer :
    (I₁) = ((X').fromSpecResidueField (reverseCenter (IsLocalRing.closedPoint ℂ))).ker :=
  (ρ.mutationTargetCenterIdeal_eq b hOpp c).trans (reverseCenter).ker_eq_ker_fromSpecResidueField

private theorem isClosedPointTower_mutationTarget :
    IsClosedPointTower X' (P(I₁)) :=
  .snoc .nil _ (isClosed_reverseCenter ρ b hOpp c)
    (mutationTargetCenterIdeal_eq_residueFieldKer ρ b hOpp c)

private theorem bidegree_lt_of_section_link (j : Fin (n + 1)) (x : Fin (n + 1) → ℤ) (d : ℤ)
    (hx : ∀ l, 0 ≤ -x l) (hm : -x j ≤ d) (hhigh : d < 2 * (-x j)) :
    let x' := Function.update (reorder(j,x)) k (-d - x j)
    hirzebruchSarkisovBidegree d.toNat (∑ l, -x' l).toNat <
      hirzebruchSarkisovBidegree d.toNat (∑ l, -x l).toNat := by
  intro x'
  let m : Fin (1 + n) → ℤ := fun l ↦ -reorder(j,x) l
  have hm₀ : m k = -x j := congrArg Neg.neg (Fin.addCases_left (0 : Fin 1))
  have hnonneg : ∀ l, 0 ≤ m l := by
    refine Fin.addCases ?_ ?_
    · intro l
      simpa only [m, Fin.addCases_left] using hx j
    · intro l
      simpa only [m, Fin.addCases_right, Function.comp_apply] using hx (j.succAbove l)
  have hsum : (∑ l, m l) = ∑ l, -x l := by
    rw [Fin.sum_univ_add (a := 1) (b := n), Fin.sum_univ_one, Fin.sum_univ_succAbove _ j]
    simp only [m, Fin.addCases_left, Fin.addCases_right, Function.comp_apply]
  have hneg : (fun l ↦ -x' l) = Function.update m k (d - m k) := by
    funext l
    dsimp only [x']
    rw [Function.apply_update (fun _ (z : ℤ) ↦ -z)]
    simp only [m, Fin.addCases_left, neg_sub, sub_neg_eq_add, add_comm]
  have hlt := hirzebruchSarkisovBidegree_elementaryTransform_lt k hnonneg
    (hm₀.symm ▸ hm) (hm₀.symm ▸ hhigh)
  simpa only [hsum, hneg] using hlt

variable {W : Scheme.{0}} {T₀ : BlowupTower Φ.algebraicRealization (n + 1) W}
  (hT₀ : IsClosedPointTower Φ.algebraicRealization T₀)

private theorem baseCenters_mutationTarget {Y : Scheme} {T : BlowupTower (I₀).blowup n Y}
    (hT : IsClosedPointTower (I₀).blowup T) (j : Fin (n + 1))
    (hcenter : ∀ l : Fin n, (I₀).blowupToBase (hT.baseCenter l) = hT₀.baseCenter (j.succAbove l)) :
    let R := T.transport (E)
    let hU := (isClosedPointTower_mutationTarget ρ b hOpp c).append
      (R.isLift.isClosedPointTower hT)
    hU.baseCenter k = reverseCenter (IsLocalRing.closedPoint ℂ) ∧
      ∀ l : Fin n, ∃ p : (I₀).blowup,
        (I₀).blowupToBase p = hT₀.baseCenter (j.succAbove l) ∧
        (I₁).blowupToBase ((E).hom p) = hU.baseCenter (l.natAdd 1) := by
  intro R hU
  dsimp only [hU]
  have hR := R.isLift.isClosedPointTower hT
  have hPivot := isClosedPointTower_mutationTarget ρ b hOpp c
  constructor
  · have hk : (0 : Fin 1) = Fin.last 0 := Fin.ext rfl
    rw [IsClosedPointTower.baseCenter_append_castAdd hPivot hR, hk,
      IsClosedPointTower.baseCenter_snoc_last, toBase_nil,
      IsClosedPointTower.lastCenter_eq _ _ (isClosed_reverseCenter ρ b hOpp c)
        (mutationTargetCenterIdeal_eq_residueFieldKer ρ b hOpp c)]
    rfl
  · intro l
    refine ⟨hT.baseCenter l, hcenter l, ?_⟩
    rw [IsClosedPointTower.baseCenter_append_natAdd hPivot hR, ← R.isLift.hom_baseCenter hT hR,
      toBase_snoc, toBase_nil, Category.comp_id]

/-- A specified point resolution with a center at the binomial point of a ruling
section transports across the smooth elementary link. Move the first center
over that point to the front and retain the relative order of every other
center, including infinitely near centers. The link agrees with the projection
of the resulting tower as a rational map on the resolved surface. The
isomorphism of resolved surfaces is over the complex field.

The first new center is the reverse pivot. Every later center projects from the
same point of the common pivot blowup as the corresponding original center.
The centers on the successive strict transforms of the pivot ray divisor are
the retained centers that were on those transforms before the mutation.

In ruling coordinates the resolved class `a F + d S` has new base class
`(a - m + d) F' + d S'` if the point lies on the chosen section, and
`(a - m) F' + d S'` if it lies on the opposite section. The order at the
reverse center is `d - m`. If `d / 2 < m ≤ d` and the other orders are
nonnegative, the Sarkisov bidegree strictly decreases. -/
theorem Ray.exists_sarkisov_decrease_of_smooth_section_center (j : Fin (n + 1))
    (hj : hT₀.baseCenter j = center (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT₀.baseCenter l ≠ center (IsLocalRing.closedPoint ℂ)) :
    let : Nonempty Φ.cones := ⟨ρ.toCone⟩
    let : Nonempty (Ψ).cones := ⟨(r ρ).toCone⟩
    let : ∀ x : X, UniqueFactorizationMonoid ((X).presheaf.stalk x) :=
      Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
    let : ∀ x : X', UniqueFactorizationMonoid ((X').presheaf.stalk x) :=
      (Ψ).uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
    let : SmoothOfRelativeDimension 2 (X ↘ B) := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsIntegral W := hT₀.isIntegral (X ↘ B)
    let : IsModification T₀.toBase :=
      hT₀.isModification_of_smoothOfRelativeDimension_two (X ↘ B)
    ∃ (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (e : W ≅ Z)
        (hU : IsClosedPointTower X' U),
      e.hom ≫ U.toBase ≫ (X' ↘ B) = T₀.toBase ≫ (X ↘ B) ∧
      T₀.toBase.toRationalMap.comp μ = (e.hom ≫ U.toBase).toRationalMap ∧
      hU.baseCenter k = reverseCenter (IsLocalRing.closedPoint ℂ) ∧
      (∀ l : Fin n, ∃ p : (I₀).blowup,
        (I₀).blowupToBase p = hT₀.baseCenter (j.succAbove l) ∧
        (I₁).blowupToBase ((E).hom p) = hU.baseCenter (l.natAdd 1)) ∧
      sectionCenters(hU,hΨ,r ρ) =
        (Finset.univ.filter fun l : Fin n ↦
          j.succAbove l ∈ sectionCenters(hT₀,hΦ,ρ)).map (Fin.natAddEmb 1) ∧
      ∀ (onSection : Bool) (a d : ℤ) (x : Fin (n + 1) → ℤ),
        let τ := if onSection then ρ else q
        let S := Additive.ofMul (primeDivisorClass (Φ.rayBoundaryPoint hΦ τ))
        let S' := Additive.ofMul (primeDivisorClass ((Ψ).rayBoundaryPoint hΨ (r τ)))
        let x' := Function.update (reorder(j,x)) k (-d - x j)
        pullback e.inv (T₀.picardHom (a • F + d • S, x)).toMul =
          (U.picardHom ((a + x j + (if onSection then d else 0)) • F' + d • S', x')).toMul ∧
        ((∀ l, 0 ≤ -x l) → -x j ≤ d → d < 2 * (-x j) →
          hirzebruchSarkisovBidegree d.toNat (∑ l, -x' l).toNat <
            hirzebruchSarkisovBidegree d.toNat (∑ l, -x l).toNat) := by
  intro h₀ h₁ huf₀ huf₁ hdim hW hdom
  let := h₀
  let := h₁
  let := huf₀
  let := huf₁
  let := hdim
  let := hW
  let := hdom
  have hI : (I₀) = ((X).fromSpecResidueField (center (IsLocalRing.closedPoint ℂ))).ker :=
    (ρ.mutationSourceCenterIdeal_eq b c).trans (center).ker_eq_ker_fromSpecResidueField
  -- Identify the first blowup with the binomial blowup before transporting the tail.
  have hmove :=
    hT₀.exists_move_closed_point_blowup_to_front j (isClosed_mutationSourcePoint ρ b c) hj hfirst
  rw [← hI] at hmove
  obtain ⟨Z, T, e, hT, he, hE, hcenter, hTail⟩ := hmove
  let R := T.transport E
  let U := (P(I₁)).append R.tower
  have hTarget := isClosedPointTower_mutationTarget ρ b hOpp c
  have hR := R.isLift.isClosedPointTower hT
  have hU : IsClosedPointTower X' U := hTarget.append hR
  obtain ⟨hreverse, hcenters⟩ := baseCenters_mutationTarget ρ b hOpp c hT₀ hT j hcenter
  have hSource : IsClosedPointTower X (P(I₀)) :=
    .snoc .nil _ (isClosed_mutationSourcePoint ρ b c) hI
  have hsection := ρ.strictTransformCenterIndices_mutation_pivot b hOpp c hΦ
    hT₀ hSource hTarget hT hR j e R.iso R.isLift he hE hTail hreverse
  let f := e.hom ≫ T.toBase
  have hf : f ≫ (I₀).blowupToBase = T₀.toBase := (Category.assoc _ _ _).trans he
  have hlink := ρ.mutationPartialMap_resolved_of_comp_eq b hOpp c f T₀.toBase hf
  have hproj : (e ≪≫ R.iso).hom ≫ U.toBase = f ≫ (E).hom ≫ (I₁).blowupToBase := by
    simp only [U, f, Iso.trans_hom, toBase_append, toBase_snoc, toBase_nil, Category.comp_id,
      Category.assoc, R.isLift.hom_toBase_assoc]
  have hover : (e ≪≫ R.iso).hom ≫ U.toBase ≫ (X' ↘ B) = T₀.toBase ≫ (X ↘ B) := by
    rw [← Category.assoc, hproj]
    simp only [Category.assoc, Fan.algebraicRealization_over,
      ρ.mutationBlowupIso_hom_comp_toBase b hOpp c, reassoc_of% hf]
  refine ⟨_, U, e ≪≫ R.iso, hU, hover,
    hlink.trans (congrArg Scheme.Hom.toRationalMap hproj.symm), hreverse, hcenters, hsection, ?_⟩
  intro onSection a d x τ S S' x'
  have hfirst' : reorder(j,x) k = x j := Fin.addCases_left _
  constructor
  · rw [Iso.trans_inv, ← pullback_comp,
      T₀.pullback_picardHom_move_to_front j e he hE hTail,
      picardHom_transport_mutation b ρ hOpp c hΦ T onSection a d (reorder(j,x))]
    simp only [hfirst', x', U, R, S', τ]
  · exact bidegree_lt_of_section_link j x d

end Resolution

end TauCeti.Toric.Fan
