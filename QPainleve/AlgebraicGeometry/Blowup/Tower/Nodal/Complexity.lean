/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity

import QPainleve.AlgebraicGeometry.Blowup.Point.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes

/-!
# Boundary complexity under nodal blowups

For a surface with a boundary divisor, the complexity is its Picard rank plus two
minus the number of boundary prime divisors. Blowing up a node adds one exceptional
coordinate to the Picard group and one prime to the reduced total boundary. This is
the corner blowup invariance of the charge in Friedman's
*On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

open Scheme.IdealSheafData

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} [IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
  {D : X.IdealSheafData} {n : ℕ} {T : BlowupTower X n Y}

/-- A nodal boundary tower adds one prime to the total boundary at each blowup. -/
theorem encard_boundaryPrimes_comap (hT : IsNodalBoundaryTower D f (𝟙 X) T) :
    (D.comap T.toBase).boundaryPrimes.encard = D.boundaryPrimes.encard + n := by
  induction hT with
  | nil => simp
  | @snoc m W R I hR p hp hI hnode ih =>
    subst I
    have := R.isNoetherian
    have := hR.isClosedPointTower.smoothOfRelativeDimension f
    have hDp : p ∈ (D.comap R.toBase).support := by
      simpa only [Category.comp_id] using mem_support_of_isNodeOfReducedBoundary hnode
    rw [toBase_snoc, comap_comp,
      encard_boundaryPrimes_comap_pointBlowup _ (R.toBase ≫ f) hp hDp, ih]
    push_cast
    rw [add_assoc]

/-- The complexity is unchanged by a tower of nodal blowups. The reduced total boundary
has the same support as the ideal pulled back along the tower. -/
theorem boundaryComplexity_comap [IsIntegral X] [X.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [Module.Finite ℤ (Additive (LineBundleClass X))] (hD : D.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T) :
    (D.comap T.toBase).boundaryComplexity = D.boundaryComplexity := by
  have hcount := hT.encard_boundaryPrimes_comap _
  have hfinite := hD.finite_boundaryPrimes
  have hncard := congrArg ENat.toNat hcount
  have hcard : (D.comap T.toBase).boundaryPrimes.ncard = D.boundaryPrimes.ncard + n := by
    simpa only [Set.ncard_def, ENat.toNat_add hfinite.encard_lt_top.ne
      (ENat.natCast_ne_top n), ENat.toNat_natCast] using hncard
  rw [boundaryComplexity_def, boundaryComplexity_def,
    finrank_picard k hT.isClosedPointTower, hcard]
  push_cast
  ring

end QPainleve.BlowupTower.IsNodalBoundaryTower
