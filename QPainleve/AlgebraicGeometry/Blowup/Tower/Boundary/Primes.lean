/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Boundary primes under closed point blowup towers

A prime of a pulled-back boundary survives precisely away from the centre of
the tower projection.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X]
  {n : ℕ} {T : BlowupTower X n Y} {D : X.IdealSheafData}

/-- A prime of the pulled-back boundary maps to the centre of the projection exactly when
its image is not a boundary prime downstairs. -/
theorem toBase_mem_centre_iff_notMem_boundaryPrimes (hT : IsClosedPointTower X T)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {x : Y} (hx : x ∈ (D.comap T.toBase).boundaryPrimes) :
    T.toBase x ∈ T.toBase.centre ↔ T.toBase x ∉ D.boundaryPrimes := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have : IsIntegral Y := hT.isIntegral f
  have := hT.isModification_of_smoothOfRelativeDimension_two f
  rw [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe]
  exact not_congr (D.mem_boundaryPrimes_iff_mem_isoLocus_of_mem_boundaryPrimes_comap _ hx).symm

end QPainleve.BlowupTower.IsClosedPointTower
