/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Cartier
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Nodality
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Reduced boundaries of nodal blowup towers

The reduced total transform of a nodal Cartier divisor remains a nodal Cartier
divisor at every stage of a tower of point blowups at its nodes.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X] [IsNoetherian X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  {n : ℕ} {T : BlowupTower X n Y}

/-- A nodal point blowup tower of a smooth surface has a nodal Cartier reduced
total boundary. Applying this to a prefix gives the same property at that stage,
including at exceptional components over self-nodes. -/
theorem radical_comap_toBase (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k))) :
    let R := (D.comap T.toBase).radical
    R.IsEffectiveCartier ∧
      AtWorstNodalOfRelativeDimensionOne (R.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k)) := by
  induction hT with
  | nil =>
    have : IsReduced D.subscheme := hN.isReduced
    dsimp only
    rw [toBase_nil, comap_id, D.isReduced_subscheme_iff_radical_eq.mp inferInstance,
      Category.id_comp]
    exact ⟨hD, hN⟩
  | @snoc m Z U I hU p hp hI hnode ih =>
    let s := U.toBase ≫ X ↘ Spec (CommRingCat.of k)
    let P := (D.comap U.toBase).radical
    let : Z.Over (Spec (.of k)) := ⟨s⟩
    have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ Spec (.of k))
    have : IsIntegral Z := hU.isClosedPointTower.isIntegral (X ↘ Spec (.of k))
    have : IsProper U.toBase := U.isProper_toBase
    have : QuasiCompact (Z ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (U.toBase ≫ X ↘ Spec (.of k)))
    have hn : P.IsNodeOfReducedBoundary s p := by
      simpa only [P, s, isNodeOfReducedBoundary_radical, Category.comp_id] using hnode
    obtain ⟨hP, hNP⟩ := ih
    have hNP' : AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ s) := hNP
    have : IsReduced P.subscheme := hNP'.isReduced
    obtain ⟨q, hq⟩ := P.range_subschemeι.ge (mem_support_of_isNodeOfReducedBoundary hn)
    subst p
    subst I
    dsimp only
    rw [Z.ker_fromSpecResidueField_eq_vanishingIdeal, toBase_snoc, Category.assoc, comap_comp]
    let J := vanishingIdeal (Closeds.closure ({P.subschemeι q} : Set Z))
    have hrad : ((D.comap U.toBase).comap J.blowupToBase).radical =
        (P.comap J.blowupToBase).radical := by
      rw [← vanishingIdeal_support, ← vanishingIdeal_support (I := P.comap _),
        support_comap ((D.comap U.toBase)), support_comap P]
      rfl
    -- Name the center and the structure morphism before rewriting the boundary ideal.
    change ((D.comap U.toBase).comap J.blowupToBase).radical.IsEffectiveCartier ∧
      AtWorstNodalOfRelativeDimensionOne
        (((D.comap U.toBase).comap J.blowupToBase).radical.subschemeι ≫ J.blowupToBase ≫ s)
    rw [hrad]
    exact ⟨hP.radical_comap_blowupToBase_of_closedPoint (Z ↘ Spec (.of k)) hp
      (mem_support_of_isNodeOfReducedBoundary hn),
      atWorstNodalOfRelativeDimensionOne_radical_comap_blowupToBase_of_node hNP' hP hp hn⟩

end QPainleve.BlowupTower.IsNodalBoundaryTower
