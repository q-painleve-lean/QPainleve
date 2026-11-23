/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Complexity
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime
public import QPainleve.Geometry.Toric.Fan.Picard.Rank

import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# The number of internal centers in a toric presentation

Boundary complexity counts the internal centers of any ordered toric presentation,
including repeated centers. The toric Picard sequence gives the starting rank,
and the Picard marking adds one coordinate per internal blowup. The strict ray
divisors account for all boundary primes. Nodal blowups preserve complexity,
so the count also holds on the original surface.

See Friedman, *On the geometry of anticanonical pairs*, Lemmas 1.2 and 2.2, for
the charge and its behavior under internal and corner blowups.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones]
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N)
  {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "P" => internalBlowupTower b s c
local notation "B" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd P))
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

include hΦ in
/-- The strict-transform boundary of the ordered internal blowup model has one prime
for each original ray, including when some centers are infinitely near. -/
theorem ncard_boundaryPrimes_internalBlowupTower :
    (B).boundaryPrimes.ncard = Nat.card Φ.Ray := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (internalBlowupBoundaryPrimeEquiv hΦ b s c).symm

include hΦ in
/-- The boundary complexity of the ordered toric blowup model equals its number of centers. -/
theorem boundaryComplexity_internalBlowupTower (hc : Φ.IsComplete) :
    (B).boundaryComplexity = (n : ℤ) := by
  have h := finrank_picard_add_finrank_eq_natCard_ray hΦ hc
  rw [rankTwo] at h
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (.of ℂ)) := by
    rw [algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let := Fintype.ofFinite Φ.Ray
  let : Module.Finite ℤ (Additive (LineBundleClass Φ.algebraicRealization)) :=
    Module.Finite.of_surjective (Φ.rayDivisorToPicard hΦ).toIntLinearMap
      (Φ.rayDivisorToPicard_surjective hΦ)
  rw [boundaryComplexity_def, ncard_boundaryPrimes_internalBlowupTower hΦ b s c,
    finrank_picard ℂ (isClosedPointTower_internalBlowupTower b s c), ← h]
  push_cast
  ring

variable {X Y : Scheme} [IsNoetherian X] [IsIntegral X] [X.Over (Spec (.of ℂ))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))]
  [Module.Finite ℤ (Additive (LineBundleClass X))]
  {A : X.IdealSheafData} {d : ℕ} {U : QPainleve.BlowupTower X d Y}

include hΦ in
/-- The complexity of a pair with a specified toric presentation counts its internal
centers. The nodal tower and the internal tower may each be empty. -/
theorem boundaryComplexity_eq_length_of_toricPresentation (hc : Φ.IsComplete)
    (hA : A.IsEffectiveCartier)
    (hU : IsNodalBoundaryTower A (X ↘ Spec (.of ℂ)) (𝟙 X) U)
    (e : Y ≅ (P).1) (he : ((A.comap U.toBase).comap e.inv).support = (B).support) :
    A.boundaryComplexity = (n : ℤ) := by
  calc
    _ = (A.comap U.toBase).boundaryComplexity := (hU.boundaryComplexity_comap hA).symm
    _ = ((A.comap U.toBase).comap e.inv).boundaryComplexity :=
      (boundaryComplexity_comap_iso e.symm _).symm
    _ = (B).boundaryComplexity := boundaryComplexity_eq_of_support_eq he
    _ = _ := boundaryComplexity_internalBlowupTower hΦ b s c hc

end TauCeti.Toric.Fan
