/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import Mathlib.Topology.KrullDimension

/-!
# Finiteness of the boundary primes of an effective Cartier divisor

An effective Cartier divisor on an integral Noetherian scheme has finitely many
boundary primes because its support is closed and omits the generic point.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme}

/-- An effective Cartier divisor on an integral Noetherian scheme has finitely many primes. -/
theorem IsEffectiveCartier.finite_boundaryPrimes [IsIntegral X] [IsNoetherian X]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) : D.boundaryPrimes.Finite := by
  let : QuasiSober (D.support : Set X) :=
    D.support.isClosed.isClosedEmbedding_subtypeVal.quasiSober
  rw [show D.boundaryPrimes = {x : X | x ∈ D.support ∧ Order.coheight x = 1} from
    Set.ext fun _ ↦ mem_boundaryPrimes]
  apply NoetherianSpace.finite_coheight_one_of_closure_ne_univ (p := (D.support : Set X))
  rw [D.support.isClosed.closure_eq]
  exact fun h ↦ hD.genericPoint_notMem_support
    (show genericPoint X ∈ (D.support : Set X) from h.symm ▸ Set.mem_univ _)

end AlgebraicGeometry.Scheme.IdealSheafData
