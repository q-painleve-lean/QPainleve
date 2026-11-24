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
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension

/-!
# Boundary primes of effective Cartier divisors

An effective Cartier divisor on an integral Noetherian scheme has finitely many
boundary primes because its support is closed and omits the generic point. Isomorphisms
of the divisor schemes identify their ambient boundary primes.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass

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

/-- The ideal of a reduced effective Cartier divisor with exactly two prime
components is the product of their vanishing ideals. -/
theorem IsEffectiveCartier.eq_mul_vanishingIdeal_of_boundaryPrimes
    [IsIntegral X] [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {D : X.IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
    {s t : D.boundaryPrimes} (hst : s ≠ t) (hall : ∀ j : D.boundaryPrimes, j = s ∨ j = t) :
    D = vanishingIdeal ⟨closure {(s : X)}, isClosed_closure⟩ *
      vanishingIdeal ⟨closure {(t : X)}, isClosed_closure⟩ := by
  classical
  let p := D.boundaryPrimeEmbedding
  have hmem (a : CodimensionOnePoint X) :
      a ∈ ({p s, p t} : Finset _) ↔ (a : X) ∈ D.support := by
    refine Iff.trans ?_ (Set.ext_iff.mp D.range_boundaryPrimeEmbedding a)
    simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_range]
    grind
  simpa only [Finset.prod_pair (p.injective.ne hst), p, coe_boundaryPrimeEmbedding] using
    hD.eq_prod_vanishingIdeal_of_isReduced _ hmem

/-- A morphism restricting to an isomorphism of effective Cartier divisors
gives a bijection of their ambient boundary primes. -/
theorem IsEffectiveCartier.bijOn_boundaryPrimes_of_subschemeIso
    {Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {D : X.IdealSheafData} {E : Y.IdealSheafData}
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (f : X ⟶ Y) (e : D.subscheme ≅ E.subscheme)
    (he : e.hom ≫ E.subschemeι = D.subschemeι ≫ f) :
    Set.BijOn f D.boundaryPrimes E.boundaryPrimes := by
  have hf (x : D.subscheme) : f (D.subschemeι x) = E.subschemeι (e.hom x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g : D.subscheme ⟶ Y ↦ g x) he.symm
  have hprime (x : D.subscheme) :
      D.subschemeι x ∈ D.boundaryPrimes ↔ E.subschemeι (e.hom x) ∈ E.boundaryPrimes := by
    have hDmem : D.subschemeι x ∈ D.support := by
      rw [← SetLike.mem_coe, ← D.range_subschemeι]
      exact Set.mem_range_self x
    have hEmem : E.subschemeι (e.hom x) ∈ E.support := by
      rw [← SetLike.mem_coe, ← E.range_subschemeι]
      exact Set.mem_range_self (e.hom x)
    simp only [mem_boundaryPrimes, hDmem, hEmem, true_and, hD.coheight_subschemeι_eq_one_iff,
      hE.coheight_subschemeι_eq_one_iff, coheight_eq_of_isOpenImmersion e.hom]
  have hsource (x : X) (hx : x ∈ D.boundaryPrimes) : x ∈ Set.range D.subschemeι := by
    rw [D.range_subschemeι]
    exact (mem_boundaryPrimes.mp hx).1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := hsource x hx
    rw [hf]
    exact (hprime a).mp hx
  · intro x hx y hy hxy
    obtain ⟨a, rfl⟩ := hsource x hx
    obtain ⟨b, rfl⟩ := hsource y hy
    rw [hf, hf] at hxy
    exact congrArg D.subschemeι
      (e.hom.isOpenEmbedding.injective (E.subschemeι.isClosedEmbedding.injective hxy))
  · intro y hy
    have hyrange : y ∈ Set.range E.subschemeι := by
      rw [E.range_subschemeι]
      exact (mem_boundaryPrimes.mp hy).1
    obtain ⟨b, rfl⟩ := hyrange
    obtain ⟨a, rfl⟩ := e.hom.surjective b
    exact ⟨D.subschemeι a, (hprime a).mpr hy, hf a⟩

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
