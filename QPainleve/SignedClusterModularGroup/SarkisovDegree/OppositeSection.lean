/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Mutation.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Picard.Quadric
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SmoothSection

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Picard.Mutation.Basic

/-!
# The return to the quadric in the two-center Sarkisov block

A smooth pivot on the section opposite the negative section of the first
Hirzebruch surface gives a resolution over the quadric. Exchanging the
quadric rulings puts the new ruling coefficient in the position used by
the Sarkisov degree. The isomorphisms of resolving surfaces track the
specified projection and the ordered exceptional coordinates.

This is the second elementary transformation and final ruling exchange
in Case B of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.Toric

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])

local notation "v" => Fan.Ray.primitiveGenerator (r 2)
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero (r 2)
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem (r 2)

local notation "hop" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch_section_two b 1 r hr
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp hop) hc
local notation "s" => r.trans (Φ.mutationFanRayEquiv b hv hp hop)
local notation "S" => Spec (CommRingCat.of k₀)
local notation "X" => (Φ.finiteFanScheme k₀)
local notation "X'" => Fan.finiteFanScheme k₀ Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis k₀ b 1 hΦ r hr
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pivot[" c "]" =>
  (Fan.Ray.binomialCenter (r 2) k₀ rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter (r 2) b) c) (IsLocalRing.closedPoint k₀)
local notation "mutation[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap k₀ b (c : k₀) hv hp hop)

local notation "C'[" d "," hs "]" => Fan.hirzebruchPicardBasis k₀ d 0 hΨ s hs

variable {n : ℕ} {Y : Scheme.{0}} {T : BlowupTower (Φ.finiteFanScheme k₀) (n + 1) Y}
  (hT : IsClosedPointTower (Φ.finiteFanScheme k₀) T)

local notation "first" => Fin.castAdd n (0 : Fin 1)
local notation "τ[" d "," hs "]" =>
  FanHom.finiteFanSchemeHom k₀ (FanEquiv.toFanHom (Fan.quadricRulingExchange d hΨ hcΨ s hs))

local notation "orders[" j "," x "," β "]" =>
  Function.update (Fin.addCases (fun _ : Fin 1 ↦ x j) (x ∘ Fin.succAbove j)) first (-β - x j)

private theorem quadricReturn_coordinates {d : Basis (Fin 2) ℤ N}
    (hs : (fun k ↦ (s k).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
    [Nonempty (Ψ).cones] [SmoothOfRelativeDimension 2 fX']
    {Z : Scheme} {U : BlowupTower X' (1 + n) Z} (hU : IsClosedPointTower X' U)
    (j : Fin (n + 1)) (a β : ℤ) (x : Fin (n + 1) → ℤ) (L : LineBundleClass Z)
    (hz : (U.picardMarking hU fX').symm (Additive.ofMul L) =
      ((a + x j) • C'[d,hs] 0 + β • C'[d,hs] 1, orders[j,x,β])) :
    let q := U.transport (asIso τ[d,hs])
    let hQ := q.isLift.isClosedPointTower hU
    let y := (q.tower.picardMarking hQ fX').symm (Additive.ofMul (pullback q.iso.inv L))
    C'[d,hs].repr y.1 0 = β ∧ C'[d,hs].repr y.1 1 = a + x j ∧
      y.2 first = -β - x j ∧ ∀ l : Fin n, y.2 (l.natAdd 1) = x (j.succAbove l) := by
  intro q hQ y
  have hswap := hU.picardMarking_symm_rulingExchange k₀ d hΨ hcΨ s hs L
  simp only [hz] at hswap
  have hrepr := C'[d,hs].repr_sum_self (![a + x j, β] : Fin 2 → ℤ)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hrepr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Equiv.swap_apply_left, congrFun hrepr (1 : Fin 2), Matrix.cons_val_one,
      Matrix.cons_val_zero] using hswap.1 (0 : Fin 2)
  · simpa only [Equiv.swap_apply_right, congrFun hrepr (0 : Fin 2), Matrix.cons_val_zero]
      using hswap.1 (1 : Fin 2)
  · simpa only [Function.update_self] using congrFun hswap.2 first
  · intro l
    have hne : l.natAdd 1 ≠ first := by
      rw [← Fin.val_ne_iff, Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero]
      omega
    exact (congrFun hswap.2 (l.natAdd 1)).trans (by
      simp only [Function.update_of_ne hne, Fin.addCases_right, Function.comp_apply])

/-- Mutation at the smooth binomial point on the opposite section of the first
Hirzebruch surface, followed by ruling exchange, transports a specified closed
point resolution to the quadric. Both projections are given on the original
resolving surface by the prescribed partial composites.

For original base coefficients a and b and pivot order m, the final base
coefficients are b and a − m. The first exceptional coefficient is m − b.
Every other coordinate retains its relative order, including at infinitely near centers. -/
theorem exists_quadric_resolution_of_hirzebruchOne_mutation
    (c : k₀ˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivot[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivot[c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΦ
    let : SmoothOfRelativeDimension 2 fX' := by
      rw [Fan.finiteFanScheme_over k₀]
      exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ hΨ
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    ∃ (d : Basis (Fin 2) ℤ N)
      (hs : (fun k ↦ (s k).primitiveGenerator) = ![d 0, d 1, -d 0, (0 : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (hU : IsClosedPointTower X' U) (e : Y ≅ Z),
      let q := U.transport (asIso τ[d,hs])
      let hQ := q.isLift.isClosedPointTower hU
      T.toBase.toRationalMap.comp mutation[c] = (e.hom ≫ U.toBase).toRationalMap ∧
      (T.toBase.toRationalMap.comp mutation[c]).compHom τ[d,hs] =
        ((e ≪≫ q.iso).hom ≫ q.tower.toBase).toRationalMap ∧
      (e ≪≫ q.iso).hom ≫ q.tower.toBase ≫ fX' = T.toBase ≫ fX ∧
      ∀ L : LineBundleClass Y,
        let x := (T.picardMarking hT fX).symm (Additive.ofMul L)
        let y := (q.tower.picardMarking hQ fX').symm (Additive.ofMul (pullback (e ≪≫ q.iso).inv L))
        C'[d,hs].repr y.1 0 = (C).repr x.1 1 ∧
        C'[d,hs].repr y.1 1 = (C).repr x.1 0 + x.2 j ∧
        y.2 first = -(C).repr x.1 1 - x.2 j ∧
        ∀ l : Fin n, y.2 (l.natAdd 1) = x.2 (j.succAbove l) := by
  intro hcones hcones' hdim hdim' hY hmod
  let := hcones
  let := hcones'
  let := hdim
  let := hdim'
  let := hY
  let := hmod
  obtain ⟨d, hd₀, hd₁, hs⟩ :=
    (r 2).mutationFan_hirzebruch_ray_generators b hop 1 r hr false rfl
  simp only [Bool.false_eq_true, ↓reduceIte, sub_self] at hd₁ hs
  obtain ⟨Z, U, e, hU, hover, hmap, -, -, -, hcoords⟩ :=
    (r 2).exists_sarkisov_decrease_of_smooth_section_center b hop c hΦ hT j hj hfirst
  refine ⟨d, hs, Z, U, hU, e, ?_⟩
  intro q hQ
  have hq : (e ≪≫ q.iso).hom ≫ q.tower.toBase = (e.hom ≫ U.toBase) ≫ τ[d,hs] := by
    rw [Iso.trans_hom, Category.assoc, q.isLift.hom_toBase, asIso_hom, Category.assoc]
  refine ⟨hmap, ?_, ?_, ?_⟩
  · rw [hmap, Scheme.Hom.toRationalMap_compHom, hq]
  · rw [← Category.assoc, hq, Category.assoc, comp_over τ[d,hs] S, Category.assoc, hover]
  intro L x y
  let a := (C).repr x.1 0
  let β := (C).repr x.1 1
  have hx : x.1 = a • C 0 + β • C 1 := by
    simpa only [a, β, Fin.sum_univ_two] using ((C).sum_repr x.1).symm
  have hxL : (T.picardHom x).toMul = L := by
    rw [← picardMarking_apply T hT fX, LinearEquiv.apply_symm_apply, toMul_ofMul]
  have hOppRay :
      Fan.Ray.ofPrimitiveGenerator (r 2).isPrimitiveGenerator.isPrimitive.neg hop = r 0 :=
    Fan.Ray.primitiveGenerator_injective (by
      have h₀ : (r 0).primitiveGenerator = b 0 := congrFun hr 0
      have h₂ : v = -b 0 := congrFun hr 2
      rw [Fan.Ray.primitiveGenerator_ofPrimitiveGenerator, h₂, neg_neg, h₀])
  have hz : (U.picardMarking hU fX').symm (Additive.ofMul (pullback e.inv L)) =
      ((a + x.2 j) • C'[d,hs] 0 + β • C'[d,hs] 1, orders[j,x.2,β]) := by
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Additive.toMul.injective
    rw [picardMarking_apply, toMul_ofMul, ← hxL]
    have h := (hcoords false a β x.2).1
    have hF := Fan.mutationFiberClass_of_opposite_section k₀ b hΦ r 1 0
      (by simpa only [zero_smul, sub_zero] using hr)
    have hF' := Fan.mutationFiberClass_of_opposite_section k₀ b hΨ s 0 1
      (by simpa only [hd₀, hd₁, one_smul] using hs)
    simp only [Equiv.trans_apply] at hF'
    have hpair : (a • C 0 + β • C 1, x.2) = x := by rw [← hx, Prod.mk.eta]
    conv_lhs => rw [← hpair]
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, hOppRay, hF, hF',
      Fan.hirzebruchPicardBasis_apply_zero, Fan.hirzebruchPicardBasis_apply_one,
      Fan.rayChartDivisorToPicard_single, one_zsmul, Equiv.trans_apply] using h
  simpa only [y, Iso.trans_inv, ← pullback_comp] using
    quadricReturn_coordinates k₀ b hΦ hc r hr hs hU j a β x.2 (pullback e.inv L) hz

end QPainleve.BlowupTower.IsClosedPointTower
