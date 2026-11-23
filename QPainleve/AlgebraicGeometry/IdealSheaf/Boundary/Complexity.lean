/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.LineBundle.Class

import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Boundary complexity

The boundary complexity is the Picard rank plus two minus the number of boundary primes.
It depends only on the support of the ideal sheaf and is invariant under scheme isomorphisms.
-/

public noncomputable section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme}

/-- The Picard rank plus two minus the number of boundary components of a surface. -/
def boundaryComplexity (D : X.IdealSheafData) : ℤ :=
  (Module.finrank ℤ (Additive (LineBundleClass X)) : ℤ) + 2 - D.boundaryPrimes.ncard

/-- Complexity is expressed using the Picard rank and the number of boundary primes. -/
theorem boundaryComplexity_def (D : X.IdealSheafData) :
    D.boundaryComplexity =
      (Module.finrank ℤ (Additive (LineBundleClass X)) : ℤ) + 2 - D.boundaryPrimes.ncard :=
  (rfl)

/-- The complexity depends only on the boundary support on a fixed scheme. -/
theorem boundaryComplexity_eq_of_support_eq {D E : X.IdealSheafData}
    (h : D.support = E.support) : D.boundaryComplexity = E.boundaryComplexity := by
  rw [boundaryComplexity_def, boundaryComplexity_def, boundaryPrimes_eq_of_support_eq h]

/-- Passing to the reduced boundary leaves the complexity unchanged. -/
@[simp]
theorem boundaryComplexity_radical (D : X.IdealSheafData) :
    D.radical.boundaryComplexity = D.boundaryComplexity :=
  boundaryComplexity_eq_of_support_eq (support_radical D)

/-- Pullback along a scheme isomorphism preserves boundary complexity. -/
@[simp]
theorem boundaryComplexity_comap_iso (e : X ≅ Y) (D : Y.IdealSheafData) :
    (D.comap e.hom).boundaryComplexity = D.boundaryComplexity := by
  have h := (LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv.finrank_eq
  rw [boundaryComplexity_def, boundaryComplexity_def, ← h, ncard_boundaryPrimes_eq_of_iso]

end AlgebraicGeometry.Scheme.IdealSheafData
