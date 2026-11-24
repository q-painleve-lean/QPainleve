/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Recovering boundary lift data from the projection

The point centers of an ordered boundary tower project to their original
boundary points. The projection also determines the strict boundary embedding
among lifts of the original boundary inclusion.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {X D : Scheme.{u}} {n : ℕ}

namespace IsClosedPointTower

/-- The projections of the centers of an ordered boundary tower are the original
boundary points, including when some of the centers coincide. -/
theorem baseCenter_alongBoundary {i : D ⟶ X} [IsClosedImmersion i]
    {J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}}
    (hT : IsClosedPointTower X (alongBoundary i J).2.toTower) (p : Fin n → D)
    (hJ : ∀ j, (J j).val = (D.fromSpecResidueField (p j)).ker) (j : Fin n) :
    hT.baseCenter j = i (p j) := by
  induction n with
  | zero => exact j.elim0
  | succ d ih =>
    -- The witness depends on the tower, so rewrite the tower before introducing it.
    revert hT
    rw [alongBoundary_succ, WithBoundary.toTower_snoc]
    intro hT
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · rw [baseCenter_snoc_last]
      let V := alongBoundary i (fun j ↦ J j.castSucc)
      have heq : hT.lastCenter.val = V.2.boundaryι (p (Fin.last d)) := by
        apply Scheme.ker_fromSpecResidueField_inj.mp
        exact hT.lastCenter.property.2.symm.trans (by
          rw [hJ, V.2.boundaryι.map_ker_fromSpecResidueField])
      rw [heq]
      exact (Scheme.Hom.comp_apply V.2.boundaryι V.2.toTower.toBase _).symm.trans
        (congrArg (fun f : D ⟶ X ↦ f (p (Fin.last d))) V.2.boundaryι_toBase)
    · rw [baseCenter_snoc_castSucc]
      exact ih _ (fun a ↦ p a.castSucc) (fun a ↦ hJ a.castSucc) l

end IsClosedPointTower

/-- The lift of the boundary inclusion through an ordered boundary tower is unique. -/
theorem eq_boundaryι_of_comp_toBase_alongBoundary (i : D ⟶ X) [IsClosedImmersion i]
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (g : D ⟶ (alongBoundary i J).1) (hg : g ≫ (alongBoundary i J).2.toTower.toBase = i) :
    g = (alongBoundary i J).2.boundaryι := by
  induction n with
  | zero =>
    revert hg g
    rw [alongBoundary_zero, WithBoundary.toTower_nil, toBase_nil, WithBoundary.boundaryι_nil]
    simp
  | succ d ih =>
    -- Expose the last blowup in the codomain before applying its universal property.
    revert hg g
    rw [alongBoundary_succ, WithBoundary.toTower_snoc, toBase_snoc]
    intro g hg
    let P := (alongBoundary i (fun j : Fin d ↦ J j.castSucc)).2
    let A := J (Fin.last d)
    let I := A.val.map P.boundaryι
    have hbase : g ≫ I.blowupToBase = P.boundaryι :=
      ih _ _ (by simpa only [Category.assoc] using hg)
    apply I.blowup_hom_ext
    · exact hbase.trans (P.boundaryι_snoc_blowupToBase A.val A.property).symm
    · rw [hbase, comap_map_of_isClosedImmersion]
      exact A.property

end QPainleve.BlowupTower
