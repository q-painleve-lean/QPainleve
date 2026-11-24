/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Mutation.Tower
public import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SmoothSection

import QPainleve.Geometry.Toric.Fan.Mutation.Projective
import QPainleve.Geometry.Toric.Fan.Picard.Homaloidal
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Logarithmic Sarkisov reduction at a smooth section point

A smooth section pivot of order greater than half the fiber degree gives a
regular partial composite on the specified resolving surface. The transported
resolution of the map to the plane has the same pole ideal, the same fiber
degree, and a smaller total base order. The geometric inputs are
`Fan.Ray.exists_sarkisov_decrease_of_smooth_section_center` and
`Fan.Ray.mutation_projection_poleIdeal`. This is the smooth-section case of
[Lutz's Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  (b : Basis (Fin 2) ℤ N) (e : ℕ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
  (onSection : Bool)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "f[" A "]" => (X[A] ↘ S)
local notation "B[" A "," h "]" => Fan.boundaryIdeal A (Fan.IsComplete.nonempty_cones h)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "C" => Fan.hirzebruchPicardBasis b e hΦ r hr
local notation "pivotIndex" => (ite (onSection = true) (0 : Fin 4) 2)
variable (ρ : Φ.Ray)
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero ρ
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem ρ
local notation "pivot" => Fan.Ray.primitiveGenerator ρ

variable (hOpp : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) (c : ℂˣ)

local notation "Ψ" => Φ.mutationFan b (v := pivot) hv hp hOpp
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b (v := pivot) hv hp hOpp) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b (v := pivot) hv hp hOpp) hc
local notation "rayEquiv" => Fan.mutationFanRayEquiv Φ b (v := pivot) hv hp hOpp
local notation "r'" => r.trans rayEquiv
local notation "e'" => (ite (onSection = true) ((e : ℤ) + 1) ((e : ℤ) - 1))
local notation "center" =>
  Fan.Ray.binomialCenter ρ rankTwo (b.detDualEquiv_self pivot)
    (Fan.Ray.surjective_detCharacter ρ b) c
local notation "μ" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) (v := pivot) hv hp hOpp)

include hr in
private theorem chosen_section_ray (hρ : ρ = r (pivotIndex)) :
    (if onSection then ρ else Fan.Ray.ofPrimitiveGenerator ρ.isPrimitiveGenerator.isPrimitive.neg
      hOpp) = r 0 := by
  cases onSection
  · apply Fan.Ray.primitiveGenerator_injective
    simp only [ite_false, Bool.false_eq_true, Fan.Ray.primitiveGenerator_ofPrimitiveGenerator]
    have hρ₂ : ρ = r 2 := hρ
    rw [congrArg Fan.Ray.primitiveGenerator hρ₂, congrFun hr 2, congrFun hr 0]
    exact neg_neg _
  · exact hρ

private theorem section_classes [Nonempty Φ.cones] [Nonempty (Ψ).cones]
    (hρ : ρ = r (pivotIndex))
    (d : Basis (Fin 2) ℤ N) (hd₀ : d 0 = b 0)
    (hd₁ : d 1 = b 1 - (if onSection then 0 else b 0))
    (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, e' • d 0 - d 1]) :
    let C' := Fan.hirzebruchPicardBasis d e' hΨ r' hr'
    Fan.mutationFiberClass b ρ hΦ = (C) 0 ∧
    Fan.mutationFiberClass b (rayEquiv ρ) hΨ = C' 0 := by
  intro C'
  cases onSection
  · have hρ₂ : ρ = r 2 := hρ
    have hρ₂' : rayEquiv ρ = r' 2 := congrArg rayEquiv hρ₂
    rw [hρ₂', Fan.hirzebruchPicardBasis_apply_zero, Fan.hirzebruchPicardBasis_apply_zero]
    exact ⟨hρ₂.symm ▸ Fan.mutationFiberClass_of_opposite_section b hΦ r e 0 (by simpa using hr),
      Fan.mutationFiberClass_of_opposite_section b hΨ r' ((e : ℤ) - 1) 1
        (by simpa only [hd₀, hd₁, Bool.false_eq_true, ite_false, one_zsmul] using hr')⟩
  · have hρ₀ : ρ = r 0 := hρ
    have hρ₀' : rayEquiv ρ = r' 0 := congrArg rayEquiv hρ₀
    have hd₁' : d 1 = b 1 := by simpa only [ite_true, sub_zero] using hd₁
    have hdb : d = b := by
      apply DFunLike.ext
      intro l
      fin_cases l
      · exact hd₀
      · exact hd₁'
    subst d
    exact ⟨hρ₀.symm ▸ Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero b e hΦ r hr,
      hρ₀'.symm ▸ Fan.mutationFiberClass_eq_hirzebruchPicardBasis_zero b ((e : ℤ) + 1) hΨ r' hr'⟩

variable {n : ℕ} {Y : Scheme} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T)

private theorem section_baseOrder_sum_and_bidegree (j : Fin (n + 1)) (x : Fin (n + 1) → ℤ)
    (β : ℤ) (hβ : 0 < β) (hm : ∀ l, 0 ≤ -x l) (hhigh : β < 2 * (-x j)) :
    let x' : Fin (1 + n) → ℤ := Fin.addCases (fun _ : Fin 1 ↦ -β - x j) (x ∘ j.succAbove)
    (∑ l, -x' l) = (∑ l, -x l) + β + 2 * x j ∧
    hirzebruchSarkisovBidegree β.toNat (∑ l, -x' l).toNat <
      hirzebruchSarkisovBidegree β.toNat (∑ l, -x l).toNat := by
  intro x'
  have hsum : (∑ l, -x' l) = (∑ l, -x l) + β + 2 * x j := by
    rw [Fin.sum_univ_add (a := 1), Fin.sum_univ_one, Fin.sum_univ_succAbove _ j]
    simp only [x', Fin.addCases_left, Fin.addCases_right, Function.comp_apply]
    ring
  have hpos : 0 < ∑ l, -x l :=
    lt_of_lt_of_le (by omega : 0 < -x j)
      (Finset.single_le_sum (fun l _ ↦ hm l) (Finset.mem_univ j))
  refine ⟨hsum, ?_⟩
  rw [hsum, Prod.Lex.lt_iff, ofLex_hirzebruchSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
  exact Or.inr ⟨rfl, by omega⟩

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]
  (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[Φ])
  (hbir : Scheme.BirationalOver g (𝟙 P))

include hg hbir in
/-- A proper smooth section pivot of order greater than half the fiber degree
gives a Sarkisov decrease for a logarithmic Hirzebruch-to-plane resolution.
Mutation transports the specified tower, including infinitely near centers,
and identifies the regular composite on the original resolving surface. The
transported tower is over a projective surface, resolves the same plane map,
and carries the transported pole ideal. The fiber degree stays fixed, the reverse
order is the fiber degree minus the pivot order, and every other order retains
its relative position. -/
theorem exists_sarkisov_decrease_of_logarithmic_smooth_section
    (hρ : ρ = r (pivotIndex)) (j : Fin (n + 1))
    (hj : hT.baseCenter j = center (IsLocalRing.closedPoint ℂ))
    (hfirst : ∀ l < j, hT.baseCenter l ≠ center (IsLocalRing.closedPoint ℂ))
    (D : Y.IdealSheafData) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Φ] :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X[Φ] := inferInstance
    let : IsIntegral Y := hT.isIntegral f[Φ]
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let a := (C).repr x.1 0
    let β := (C).repr x.1 1
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    β < 2 * (-x.2 j) →
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 f[Ψ] :=
      rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
    let : IsNoetherian X[Ψ] := inferInstance
    X[Ψ].IsProjectiveOver ℂ ∧
    ∃ (d : Basis (Fin 2) ℤ N)
      (hr' : (fun l ↦ (r' l).primitiveGenerator) = ![d 0, d 1, -d 0, e' • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[Ψ] (1 + n) Z) (hU : IsClosedPointTower X[Ψ] U) (k : Y ≅ Z),
      T.toBase.toRationalMap.comp μ = (k.hom ≫ U.toBase).toRationalMap ∧
      k.hom ≫ U.toBase ≫ f[Ψ] = T.toBase ≫ f[Φ] ∧
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[Ψ] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      B[Ψ,hcΨ].comap U.toBase = D.comap k.inv * hU.ramificationIdealSheafToBase ℂ ∧
      let C' := Fan.hirzebruchPicardBasis d e' hΨ r' hr'
      let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback (k.inv ≫ g) H))
      (C').repr y.1 0 = a + x.2 j + (if onSection then β else 0) ∧
      (C').repr y.1 1 = β ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove) ∧
      (∑ l, -y.2 l) = (∑ l, -x.2 l) + β + 2 * x.2 j ∧
      hirzebruchSarkisovBidegree ((C').repr y.1 1).toNat (∑ l, -y.2 l).toNat <
        hirzebruchSarkisovBidegree β.toNat (∑ l, -x.2 l).toNat := by
  intro hcones hdim hnoeth hintegral hmod x a β hD hhigh hcones' hdim' hnoeth'
  let := hcones
  let := hdim
  let := hnoeth
  let := hintegral
  let := hmod
  let := hcones'
  let := hdim'
  let := hnoeth'
  refine ⟨Fan.Ray.isProjectiveOver_mutationFan ρ b hOpp hΦ, ?_⟩
  obtain ⟨d, hd₀, hd₁, hr'⟩ :=
    Fan.Ray.mutationFan_hirzebruch_ray_generators ρ b hOpp e r hr onSection hρ
  obtain ⟨Z, U, k, hU, hk, hlink, -, -, hpic⟩ :=
    Fan.Ray.exists_sarkisov_decrease_of_smooth_section_center ρ b hOpp c hΦ hT j hj hfirst
  have hg' : (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[Ψ] := by
    rw [Category.assoc, hg, ← hk, k.inv_hom_id_assoc]
  have hbir' : Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) :=
    Scheme.BirationalOver.trans (sY := g)
      ⟨.ofIso k.symm, by simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso]⟩ hbir
  refine ⟨d, hr', Z, U, hU, k, hlink, hk, hg', hbir',
    ρ.mutation_projection_poleIdeal b hOpp c hT hΦ hc hU k hlink D hD, ?_⟩
  intro C' y
  obtain ⟨hF, hF'⟩ := section_classes b e hΦ r hr onSection ρ hOpp hρ d hd₀ hd₁ hr'
  obtain ⟨hL, -⟩ := hpic onSection a β x.2
  -- Read the pullback in the transported marking, using the two Hirzebruch basis vectors.
  let := Φ.uniqueFactorizationMonoid_stalk_algebraicRealization hΦ
  let := (Ψ).uniqueFactorizationMonoid_stalk_algebraicRealization hΨ
  have hS : (C) 1 = Additive.ofMul (primeDivisorClass (Φ.rayBoundaryPoint hΦ (r 0))) := by
    classical
    rw [Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single, one_zsmul]
  have hS' : C' 1 =
      Additive.ofMul (primeDivisorClass ((Ψ).rayBoundaryPoint hΨ (rayEquiv (r 0)))) := by
    classical
    simp only [C', Fan.hirzebruchPicardBasis_apply_one, Fan.rayDivisorToPicard_single,
      one_zsmul, Equiv.trans_apply]
  simp only [chosen_section_ray b e r hr onSection ρ hOpp hρ, hF, hF', ← hS, ← hS'] at hL
  have hx : a • (C) 0 + β • (C) 1 = x.1 := by
    simpa only [Fin.sum_univ_two] using (C).sum_repr x.1
  rw [hx, ← T.picardMarking_apply hT f[Φ],
    Prod.mk.eta, LinearEquiv.apply_symm_apply, toMul_ofMul, pullback_comp] at hL
  let x' : Fin (1 + n) → ℤ := Fin.addCases (fun _ : Fin 1 ↦ -β - x.2 j) (x.2 ∘ j.succAbove)
  have hx' : Function.update (Fin.append (fun _ : Fin 1 ↦ x.2 j) (x.2 ∘ j.succAbove))
      (Fin.castAdd n (0 : Fin 1)) (-β - x.2 j) = x' := by
    rw [Fin.update_append_castAdd]
    congr 1
    funext l
    rw [Subsingleton.elim l (0 : Fin 1), Function.update_self]
  simp only [Fin.append] at hx'
  rw [hx', ← U.picardMarking_apply hU f[Ψ]] at hL
  have hy := congrArg ((U.picardMarking hU f[Ψ]).symm ∘ Additive.ofMul) hL
  simp only [Function.comp_apply, ofMul_toMul, LinearEquiv.symm_apply_apply] at hy
  have hy' : y = ((a + x.2 j + (if onSection then β else 0)) • C' 0 + β • C' 1, x') := hy
  have hcoeff : (C').repr y.1 0 = a + x.2 j + (if onSection then β else 0) ∧
      (C').repr y.1 1 = β ∧ y.2 = x' := by
    rw [hy']
    simp [-Fan.hirzebruchPicardBasis_apply_zero, -Fan.hirzebruchPicardBasis_apply_one]
  obtain ⟨ha', hβ', horders'⟩ := hcoeff
  obtain ⟨hβpos, -, hm⟩ := hT.hirzebruch_resolution_degree_bounds b e hΦ hc r hr g hg hbir
  refine ⟨ha', hβ', horders', ?_⟩
  rw [hβ', horders']
  exact section_baseOrder_sum_and_bidegree j x.2 β hβpos hm hhigh

end QPainleve.BlowupTower.IsClosedPointTower
