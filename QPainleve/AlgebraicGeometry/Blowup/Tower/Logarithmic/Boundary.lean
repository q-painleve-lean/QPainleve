/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.Order

import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.CurvePoint
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Boundary transforms in logarithmic point blowups

The pole ideal of a pulled-back logarithmic form is the total-transform ideal
divided by ramification. At a smooth boundary center this gives the strict
transform. At a node it gives the reduced total transform, including one copy
of the exceptional curve. These are the two allowed steps in the
volume-preserving factorizations of [Lutz, Definition 8.1][Lutz].

[Lutz]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData} {I : Y.IdealSheafData}

/-- If the composite pullback has no zeros and the preceding pole divisor is nodal,
the last center is on that divisor. The new pole ideal is its strict transform at a
smooth point and its reduced total transform at a node. The smooth case also gives
the Cartier center on the boundary itself, so the original boundary embeds as its
strict transform by the canonical blowup lift. -/
theorem poleIdeal_snoc_of_nodal_boundary (hD : D.IsEffectiveCartier)
    (hT : IsClosedPointTower X T) (p : Y) (hp : IsClosed ({p} : Set Y))
    (hI : I = (Y.fromSpecResidueField p).ker)
    (h : D.comap (T.snoc I).toBase ≤ (hT.snoc p hp hI).ramificationIdealSheafToBase k)
    (hnodal : let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
      AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k))) :
    let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
    let P' := (D.comap (T.snoc I).toBase).colon ((hT.snoc p hp hI).ramificationIdealSheafToBase k)
    p ∈ P.support ∧ IsReduced P'.subscheme ∧
      ((P.IsNodeOfReducedBoundary (T.toBase ≫ X ↘ Spec (.of k)) p ∧
          P' = (P.comap I.blowupToBase).radical) ∨
        (¬ P.IsNodeOfReducedBoundary (T.toBase ≫ X ↘ Spec (.of k)) p ∧
          P' = (I.blowupMap P.subschemeι).ker ∧ (I.comap P.subschemeι).IsEffectiveCartier)) := by
  let P := (D.comap T.toBase).colon (hT.ramificationIdealSheafToBase k)
  let s := T.toBase ≫ X ↘ Spec (.of k)
  let P' := (D.comap (T.snoc I).toBase).colon ((hT.snoc p hp hI).ramificationIdealSheafToBase k)
  have : SmoothOfRelativeDimension 2 s := hT.smoothOfRelativeDimension _
  obtain ⟨hP, hpP, hformula⟩ := hT.poleIdeal_snoc_of_totalTransform_le_ramification k hD p hp hI h
  have hPnodal : AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ s) := by
    simpa only [Category.assoc] using hnodal
  have hm := hP.stalkOrder_eq_if_isNodeOfReducedBoundary hPnodal hpP
  have : IsReduced P.subscheme := hPnodal.isReduced
  by_cases hnode : P.IsNodeOfReducedBoundary s p
  · have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq s 2).mp inferInstance).2 p hp
    have : Smooth s := SmoothOfRelativeDimension.smooth 2 s
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
    have := isRegularLocalRing_stalk_of_smooth s p
    have : IsReduced (I.comap I.blowupToBase).subscheme := by
      rw [hI, Y.ker_fromSpecResidueField_eq_vanishingIdeal]
      exact @isReduced_of_isIntegral _ (isIntegral_exceptional_blowup_closed_point hdim hp)
    have hPI : P ≤ I := hI ▸ (P.le_ker_fromSpecResidueField_iff_mem_support hp).mpr hpP
    rw [ite_eq_left hnode] at hm
    have heq : P' = (P.comap I.blowupToBase).radical := by
      dsimp only [P']
      rw [hformula, hm, I.radical_comap_blowupToBase_eq_ker_blowupMap_subschemeι_mul P hPI]
      simp [P]
    have hred : IsReduced P'.subscheme := by
      rw [heq, ← vanishingIdeal_support]
      infer_instance
    exact ⟨hpP, hred, Or.inl ⟨hnode, heq⟩⟩
  · rw [ite_eq_right hnode] at hm
    have heq : P' = (I.blowupMap P.subschemeι).ker := by
      dsimp only [P']
      rw [hformula, hm]
      simp [P]
    have hr : p ∈ Set.range P.subschemeι := P.range_subschemeι.symm ▸ hpP
    obtain ⟨q, hq⟩ := hr
    have hc : IsClosed ({q} : Set P.subscheme) :=
      P.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr (by
        simpa only [Set.image_singleton, hq] using hp)
    have := hPnodal.syntomic
    have hs : q ∈ (P.subschemeι ≫ s).smoothLocus := by
      by_contra hq'
      apply hnode
      exact (P.isNodeOfReducedBoundary_iff_of_isReduced s p).mpr
        ⟨q, hq, ((P.subschemeι ≫ s).isNodeAt_iff_notMem_smoothLocus hPnodal q).mpr hq'⟩
    have hcart : (I.comap P.subschemeι).IsEffectiveCartier := by
      rw [hI, ← hq, P.subschemeι.comap_ker_fromSpecResidueField_apply]
      exact (P.subschemeι ≫ s).isEffectiveCartier_ker_fromSpecResidueField_of_mem_smoothLocus hc hs
    have hred : IsReduced P'.subscheme := by
      rw [heq]
      exact I.isReduced_subscheme_ker_blowupMap P
    exact ⟨hpP, hred, Or.inr ⟨hnode, heq, hcart⟩⟩

end QPainleve.BlowupTower.IsClosedPointTower
