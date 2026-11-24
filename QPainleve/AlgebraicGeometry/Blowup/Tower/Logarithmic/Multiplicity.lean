/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Ramification

/-!
# Base multiplicities above a regular boundary component

For a tower on which the pulled-back logarithmic form has no zeros, every
center above the interior of a regular component is on its successive strict
transform. The Picard pairing then bounds the sum of the base orders over
the interior by the original intersection with the component. This gives the
interior-component estimate in [Lutz, Proposition 8.7][Lutz] for the specified
tower, including its infinitely near centers.

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=70
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass
open Scheme.IdealSheafData.IsEffectiveCartier (toInvertibleSheaf)

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D C : X.IdealSheafData}
  [IrreducibleSpace C.subscheme] [TauCeti.AlgebraicGeometry.IsRegular C.subscheme]

local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "classOf" h => (LineBundleClass.mk (toInvertibleSheaf h))⁻¹

section Logarithmic

variable [PerfectField k] [IsNoetherian X]

/-- Above a point off the residual boundary, the pole divisor is supported on the strict
transform of the regular component. This comparison uses the ramification ideal of the
actual point tower. -/
theorem poleIdeal_support_le_strictTransform_sup_residual (hT : IsClosedPointTower X T)
    (hC : C.IsEffectiveCartier) (hDC : D ≤ C) (hdim : topologicalKrullDim C.subscheme = 1) :
    ((D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)).support ≤
      (T.strictTransform C).support ⊔ ((D.colon C).comap T.toBase).support := by
  have hD := D.eq_colon_mul C hC.locallyPrincipal hDC
  have hle : ((D.colon C).comap T.toBase * T.strictTransform C) ≤
      (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k) := by
    apply le_colon_iff.mpr
    have hmul := hT.strictTransform_mul_ramification_le_totalTransform (k := k) hC hdim
    have hprod : D.comap T.toBase = (D.colon C).comap T.toBase * C.comap T.toBase := by
      rw [← comap_mul, ← hD]
    rw [mul_assoc, hprod]
    intro V
    simpa only [ideal_mul, Pi.mul_apply] using
      (Ideal.mul_mono (le_refl (((D.colon C).comap T.toBase).ideal V)) (hmul V))
  simpa only [support_mul, sup_comm] using support_antitone hle

/-- Every step above the interior of a regular component of the pole divisor has
exceptional strict-transform coefficient `-1`. Elsewhere the coefficient is nonpositive.
The interior is obtained by removing the support of the residual divisor. -/
theorem strictTransformCoefficients_of_logarithmic_tower (hT : IsClosedPointTower X T)
    (hD : D.IsEffectiveCartier) (hC : C.IsEffectiveCartier) (hDC : D ≤ C)
    (hdim : topologicalKrullDim C.subscheme = 1)
    (hlog : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k) :
    ∀ j : Fin n, hT.strictTransformCoefficients C j ≤ 0 ∧
      (hT.baseCenter j ∈ (C.support : Set X) \ (D.colon C).support →
        hT.strictTransformCoefficients C j = -1) := by
  classical
  induction hT with
  | nil => exact fun j ↦ j.elim0
  | @snoc d W U I hU p hp hI ih =>
    let V := IsClosedPointTower.nil.snoc p hp hI
    have hprev := hU.totalTransform_le_ramification_of_append k hD V
      (by simpa only [append_snoc, append_nil] using hlog)
    intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [strictTransformCoefficients_snoc_last _ _ p hp hI, baseCenter_snoc_last,
        lastCenter_eq _ p hp hI]
      refine ⟨neg_nonpos.mpr (Int.natCast_nonneg _), fun h ↦ ?_⟩
      obtain ⟨-, hpole, -⟩ := hU.poleIdeal_snoc_of_totalTransform_le_ramification k hD p hp hI hlog
      have hsupport := hU.poleIdeal_support_le_strictTransform_sup_residual hC hDC hdim hpole
      rw [← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union, support_comap,
        Closeds.coe_preimage, Set.mem_preimage] at hsupport
      have hstrict := hsupport.resolve_right h.2
      rw [hU.stalkOrder_strictTransform_eq_one_of_mem_support f hC hdim hstrict]
      rfl
    · simpa only [strictTransformCoefficients_snoc_castSucc, baseCenter_snoc_castSucc] using
        ih hprev j

end Logarithmic

variable [IsAlgClosed k] [X.IsProjectiveOver k]

open Classical in
/-- In a closed point tower carrying a pulled-back logarithmic form with no zeros, the
sum of the base orders over the interior of a regular boundary component is at most the
intersection of the original class with the component. The resolved class is nef and
has total exceptional coefficients `-m`. -/
theorem sum_base_orders_le_intersection_of_logarithmic_tower (hT : IsClosedPointTower X T)
    (hD : D.IsEffectiveCartier) (hC : C.IsEffectiveCartier) (hDC : D ≤ C)
    (hdim : topologicalKrullDim C.subscheme = 1)
    (hlog : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k)
    (a : LineBundleClass X) (m : Fin n → ℤ) (hm : ∀ j, 0 ≤ m j)
    (hnef : (T.picardHom (Additive.ofMul a, -m)).toMul.IsNef k (T.toBase ≫ f)) :
    ∑ j ∈ Finset.univ.filter
      (fun j ↦ hT.baseCenter j ∈ (C.support : Set X) \ (D.colon C).support), m j ≤
        Chow.classIntersectionNumber k X a (classOf hC) := by
  classical
  have : IsNoetherian X := isNoetherian_of_finiteType f
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  have : Y.IsProjectiveOver k := T.isProjectiveOver k
  have : IsIntegral Y := hT.isIntegral f
  have : SmoothOfRelativeDimension 2 (T.toBase ≫ f) := hT.smoothOfRelativeDimension f
  let (y : Y) := (T.toBase ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  have hdimY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (T.toBase ≫ f) (n := 2)
  have hnonneg := Chow.classIntersectionNumber_nonneg_of_isNef_of_isEffectiveCartier
    k hdimY hnef (hT.isEffectiveCartier_strictTransform f hC)
  have hclass := congrArg Additive.toMul (hT.picardMarking_strictTransform f hC)
  simp only [toMul_ofMul] at hclass
  rw [← hclass, ← T.picardMarking_apply hT f (Additive.ofMul a, -m),
    classIntersectionNumber_picardMarking k hT] at hnonneg
  rw [Finset.sum_filter]
  refine le_trans (Finset.sum_le_sum fun j _ ↦ ?_) (sub_nonneg.mp hnonneg)
  simp only [Pi.neg_apply]
  obtain ⟨hj, hcj⟩ := hT.strictTransformCoefficients_of_logarithmic_tower hD hC hDC hdim hlog j
  split
  · rename_i h
    simp [hcj h]
  · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hm j)) hj

/-- Over the interior of one regular component, at most one step has base order
greater than half the intersection of the original class with that component. -/
theorem eq_of_intersection_lt_two_mul_baseOrder_of_logarithmic_tower
    (hT : IsClosedPointTower X T)
    (hD : D.IsEffectiveCartier) (hC : C.IsEffectiveCartier) (hDC : D ≤ C)
    (hdim : topologicalKrullDim C.subscheme = 1)
    (hlog : D.comap T.toBase ≤ hT.ramificationIdealSheafToBase k)
    (a : LineBundleClass X) (m : Fin n → ℤ) (hm : ∀ j, 0 ≤ m j)
    (hnef : (T.picardHom (Additive.ofMul a, -m)).toMul.IsNef k (T.toBase ≫ f))
    {j l : Fin n}
    (hj : hT.baseCenter j ∈ (C.support : Set X) \ (D.colon C).support)
    (hl : hT.baseCenter l ∈ (C.support : Set X) \ (D.colon C).support)
    (hmj : Chow.classIntersectionNumber k X a (classOf hC) < 2 * m j)
    (hml : Chow.classIntersectionNumber k X a (classOf hC) < 2 * m l) : j = l := by
  classical
  by_contra hne
  have hsum := hT.sum_base_orders_le_intersection_of_logarithmic_tower
    hD hC hDC hdim hlog a m hm hnef
  let s := Finset.univ.filter (fun i ↦ hT.baseCenter i ∈ (C.support : Set X) \ (D.colon C).support)
  have hj' : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hl' : l ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hbound := (Finset.add_le_sum (fun i _ ↦ hm i) hj' hl' hne).trans hsum
  omega

end QPainleve.BlowupTower.IsClosedPointTower
