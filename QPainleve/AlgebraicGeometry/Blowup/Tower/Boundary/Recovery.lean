/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Projected centers of boundary blowup towers

The point centers of an ordered boundary tower project to their original
boundary points.
-/

public section

open AlgebraicGeometry CategoryTheory

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

end QPainleve.BlowupTower
