/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Bounding base orders by intersection with a curve

A regular proper curve embeds in each successive point blowup as its strict transform.
A negative total exceptional coefficient subtracts from its degree at each center on that
transform. In particular, the first blowup over each selected point of the original curve
contributes to the intersection bound, even if the tower has further infinitely near centers.
This gives the fiber separation used in Case B of Lutz's Proposition 8.11 in
[*Homological mirror symmetry for log Calabi–Yau surfaces*][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] {C X Y : Scheme.{u}}
  [C.Over (Spec (.of k))] [hC : C.IsCurveOver k]

private theorem intersectionNumber_blowupLift_twist_le (i : C ⟶ X) {p : X}
    (hp : IsClosed ({p} : Set X)) (a : LineBundleClass X) (m : ℕ)
    {take : Prop} [Decidable take] (htake : take → p ∈ Set.range i)
    (h : ((X.fromSpecResidueField p).ker.comap i).IsEffectiveCartier) :
    let I := (X.fromSpecResidueField p).ker
    intersectionNumber k (I.blowupLift i h)
      (pullback I.blowupToBase a * I.blowupExceptionalClass ^ (-(m : ℤ))) ≤
        intersectionNumber k i a - (if take then (m : ℤ) else 0) := by
  intro I
  let j := I.blowupLift i h
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have he := I.isEffectiveCartier_comap_blowupToBase
  have hj : ((I.comap I.blowupToBase).comap j).IsEffectiveCartier :=
    (I.comap_blowupLift_exceptional i h).symm ▸ h
  rw [intersectionNumber_mul_of_isIntegral, intersectionNumber_pullback,
    I.blowupLift_blowupToBase, intersectionNumber_zpow_of_isIntegral]
  have hm : 0 ≤ (m : ℤ) := Nat.cast_nonneg m
  by_cases hs : take
  · have hpos : 0 < intersectionNumber k j I.blowupExceptionalClass := by
      rw [blowupExceptionalClass_def]
      refine (intersectionNumber_inv_mk_toInvertibleSheaf_pos_iff k j he hj).mpr ?_
      obtain ⟨q, hq⟩ := htake hs
      refine ⟨q, ?_⟩
      rw [Set.mem_preimage, support_comap, Closeds.coe_preimage,
        Set.mem_preimage, ← Scheme.Hom.comp_apply, I.blowupLift_blowupToBase,
        X.support_ker_fromSpecResidueField_of_isClosed hp, hq]
      exact Set.mem_singleton _
    rw [ite_eq_left hs, neg_mul, ← sub_eq_add_neg]
    have hdeg : 1 ≤ intersectionNumber k j I.blowupExceptionalClass := by omega
    simpa only [mul_one] using sub_le_sub_left (mul_le_mul_of_nonneg_left hdeg hm)
      (intersectionNumber k i a)
  · have hnonneg : 0 ≤ intersectionNumber k j I.blowupExceptionalClass :=
      by simpa only [blowupExceptionalClass_def] using
        intersectionNumber_inv_mk_toInvertibleSheaf_nonneg k j he hj
    rw [ite_eq_right hs, sub_zero]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) hnonneg)

variable [hRegular : IsRegular C] {n : ℕ} {T : BlowupTower X n Y}

include hC hRegular in
private theorem exists_curve_lift_intersectionNumber_picardHom_le (hT : IsClosedPointTower X T)
    (i : C ⟶ X) [IsClosedImmersion i] (a : LineBundleClass X) (m : Fin n → ℕ) (s : Finset (Fin n))
    (hs : ∀ j ∈ s, (hT.baseCenter j ∈ Set.range i) ∧
      ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j) :
    ∃ j : C ⟶ Y, IsClosedImmersion j ∧ j ≫ T.toBase = i ∧
      intersectionNumber k j (T.picardHom (Additive.ofMul a, fun l ↦ -(m l : ℤ))).toMul ≤
        intersectionNumber k i a - ∑ l ∈ s, (m l : ℤ) := by
  classical
  induction hT with
  | nil =>
    refine ⟨i, inferInstance, by simp, ?_⟩
    simp [picardHom_nil, Finset.sum_of_isEmpty]
  | @snoc d W U I hU p hp hI ih =>
    subst I
    let I := (W.fromSpecResidueField p).ker
    let s' : Finset (Fin d) := Finset.univ.filter fun l ↦ l.castSucc ∈ s
    have hs' : ∀ l ∈ s', (hU.baseCenter l ∈ Set.range i) ∧
        ∀ j < l, hU.baseCenter j ≠ hU.baseCenter l := by
      intro l hl
      obtain ⟨hlC, hlFirst⟩ := hs l.castSucc (Finset.mem_filter.mp hl).2
      rw [baseCenter_snoc_castSucc] at hlC
      refine ⟨hlC, fun j hj ↦ ?_⟩
      simpa only [baseCenter_snoc_castSucc] using hlFirst j.castSucc (by exact_mod_cast hj)
    obtain ⟨j, hj, hcomp, hdeg⟩ := ih (fun l ↦ m l.castSucc) s' hs'
    have hpj : Fin.last d ∈ s → p ∈ Set.range j := by
      intro hlast
      obtain ⟨hlastC, hlastFirst⟩ := hs (Fin.last d) hlast
      rw [baseCenter_snoc_last, lastCenter_eq _ p hp rfl] at hlastC hlastFirst
      obtain ⟨q, hq⟩ := hlastC
      have havoid : U.toBase p ∉ Set.range hU.baseCenter := by
        rintro ⟨l, hl⟩
        apply hlastFirst l.castSucc (Fin.castSucc_lt_last l)
        simpa only [baseCenter_snoc_castSucc] using hl
      have hq' : U.toBase (j q) = U.toBase p := by
        rw [← Scheme.Hom.comp_apply, hcomp, hq]
      have hqavoid : U.toBase (j q) ∉ Set.range hU.baseCenter := by rwa [hq']
      exact ⟨q, hU.injOn_toBase_compl_range_baseCenter hqavoid havoid hq'⟩
    have h := j.isEffectiveCartier_comap_ker_fromSpecResidueField
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k) hp
    refine ⟨I.blowupLift j h, I.isClosedImmersion_blowupLift j h, ?_, ?_⟩
    · rw [toBase_snoc, I.blowupLift_blowupToBase_assoc, hcomp]
    · rw [picardHom_snoc_apply_toMul]
      have hstep := intersectionNumber_blowupLift_twist_le (k := k) j hp
        (U.picardHom (Additive.ofMul a, fun l ↦ -(m l.castSucc : ℤ))).toMul
        (m (Fin.last d)) hpj h
      have hsum : ∑ l ∈ s, (m l : ℤ) =
          (∑ l ∈ s', (m l.castSucc : ℤ)) + if Fin.last d ∈ s then (m (Fin.last d) : ℤ) else 0 := by
        calc
          _ = ∑ l, if l ∈ s then (m l : ℤ) else 0 := by
            rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
          _ = _ := by rw [Fin.sum_univ_castSucc, ← Finset.sum_filter]
      exact hstep.trans (by rw [hsum, ← sub_sub]; exact sub_le_sub_right hdeg _)

include hC hRegular in
/-- The orders at selected first centers over a regular proper curve sum to at most
the original degree on the curve when the resolved class is nef. The orders are the
negatives of the total exceptional coordinates of the resolved class. Other centers
may lie anywhere, including at points infinitely near a selected center. -/
theorem sum_first_base_orders_le_curve_intersection (hT : IsClosedPointTower X T)
    (i : C ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    (hi : C ↘ Spec (.of k) = i ≫ f) (a : LineBundleClass X) (m : Fin n → ℕ) (s : Finset (Fin n))
    (hs : ∀ j ∈ s, (hT.baseCenter j ∈ Set.range i) ∧
      ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hnef : (T.picardHom (Additive.ofMul a, fun l ↦ -(m l : ℤ))).toMul.IsNef k (T.toBase ≫ f)) :
    ∑ l ∈ s, (m l : ℤ) ≤ intersectionNumber k i a := by
  obtain ⟨j, hj, hcomp, hle⟩ :=
    hT.exists_curve_lift_intersectionNumber_picardHom_le (k := k) i a m s hs
  have hnonneg := hnef.intersectionNumber_nonneg j (by rwa [← Category.assoc, hcomp])
  omega

end QPainleve.BlowupTower.IsClosedPointTower
