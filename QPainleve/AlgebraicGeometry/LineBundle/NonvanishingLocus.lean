/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
import TauCeti.AlgebraicGeometry.LineBundle.Germ
import TauCeti.LinearAlgebra.Dimension.FinrankOne

/-!
# Nonvanishing at the generic point

A section of a line bundle on an integral scheme generates its generic stalk
exactly when the section is nonzero.
-/

public section

open AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} [IsIntegral X]

/-- On a nonempty open of an integral scheme, a section generates the generic stalk
if and only if it is nonzero. -/
@[simp]
theorem genericPoint_mem_nonvanishingLocus_iff (L : InvertibleSheaf X)
    {U : X.Opens} [Nonempty U] (s : Γ(L.obj, U)) :
    genericPoint X ∈ L.obj.nonvanishingLocus s ↔ s ≠ 0 := by
  let : Field X.functionField := inferInstance
  rw [Scheme.Modules.mem_nonvanishingLocus_iff_of_mem (Scheme.genericPoint_mem U),
    span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one
      (L.obj.finrank_stalk_of_isInvertible (genericPoint X))]
  exact map_ne_zero_iff _ (L.germ_injective_of_isIntegral _ (Scheme.genericPoint_mem U))

end TauCeti.AlgebraicGeometry.InvertibleSheaf
