/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic

import Mathlib.Topology.KrullDimension

/-!
# Finiteness of the boundary primes of an effective Cartier divisor

An effective Cartier divisor on an integral Noetherian scheme has finitely many
boundary primes because its support is closed and omits the generic point.
-/

public section

open TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass

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

/-- Matching the prime classes of two reduced effective Cartier divisors under an additive map
of Picard groups matches the classes of the full divisors. -/
theorem IsEffectiveCartier.map_ofMul_inv_toInvertibleSheaf_of_boundaryPrimes
    {Y : Scheme} [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {D : X.IdealSheafData} {E : Y.IdealSheafData}
    [IsReduced D.subscheme] [IsReduced E.subscheme]
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (f : Additive (LineBundleClass X) →+ Additive (LineBundleClass Y))
    (σ : D.boundaryPrimes ≃ E.boundaryPrimes)
    (hσ : ∀ p, f (Additive.ofMul (primeDivisorClass (D.boundaryPrimeEmbedding p))) =
      Additive.ofMul (primeDivisorClass (E.boundaryPrimeEmbedding (σ p)))) :
    f (Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹) =
      Additive.ofMul (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ := by
  let : Fintype D.boundaryPrimes := hD.finite_boundaryPrimes.fintype
  let : Fintype E.boundaryPrimes := hE.finite_boundaryPrimes.fintype
  rw [hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass D.boundaryPrimeEmbedding
      (fun p ↦ D.range_boundaryPrimeEmbedding.symm ▸ Iff.rfl),
    hE.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass E.boundaryPrimeEmbedding
      (fun p ↦ E.range_boundaryPrimeEmbedding.symm ▸ Iff.rfl), map_sum, ← Equiv.sum_comp σ]
  exact Finset.sum_congr rfl fun p _ ↦ hσ p

end AlgebraicGeometry.Scheme.IdealSheafData
