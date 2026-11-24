/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Complexity

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes

/-!
# Boundary complexity under point blowups

When the projection of a closed-point blowup tower identifies two effective Cartier
boundaries, their complexity difference is the length of the tower.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (k : Type u) [Field k] [PerfectField k] [IsIntegral X] [IsNoetherian X]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

include k in
/-- A point blowup projection that identifies two effective Cartier boundaries
increases the boundary complexity by the number of blowups. In particular,
contracting an internal exceptional configuration of that size removes the
same amount of complexity. -/
theorem boundaryComplexity_eq_add_length_of_subschemeIso
    [Module.Finite ℤ (Additive (LineBundleClass X))]
    (hT : IsClosedPointTower X T) {D : X.IdealSheafData} {B : Y.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hB : B.IsEffectiveCartier)
    (e : B.subscheme ≅ D.subscheme)
    (he : e.hom ≫ D.subschemeι = B.subschemeι ≫ T.toBase) :
    B.boundaryComplexity = D.boundaryComplexity + n := by
  have : IsNoetherian Y := T.isNoetherian
  have hprimes := (hB.bijOn_boundaryPrimes_of_subschemeIso hD T.toBase e he).ncard_eq
  rw [boundaryComplexity_def, boundaryComplexity_def, finrank_picard k hT, hprimes]
  push_cast
  ring

end QPainleve.BlowupTower.IsClosedPointTower
