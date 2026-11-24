/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import Mathlib.RingTheory.Nilpotent.Lemmas
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Reduction of effective Cartier divisors

On a locally factorial locally Noetherian scheme the reduced support of an
effective Cartier divisor is again effective Cartier. This allows reduced
divisors to be extended by schematic closure across open immersions.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- The reduction of an effective Cartier divisor on a locally factorial locally
Noetherian scheme is effective Cartier. -/
theorem IsEffectiveCartier.radical {X : Scheme.{u}} [IsLocallyNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier) : D.radical.IsEffectiveCartier := by
  classical
  refine (isEffectiveCartier_iff_forall_exists_map_germ_eq_span_singleton _).mpr fun U x hx ↦ ?_
  obtain ⟨a, ha, hspan⟩ := hD.exists_map_germ_eq_span_singleton U hx
  let : StrongNormalizationMonoid (X.presheaf.stalk x) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  refine ⟨UniqueFactorizationMonoid.radical a,
    IsSMulRegular.of_ne_zero UniqueFactorizationMonoid.radical_ne_zero, ?_⟩
  rw [radical_ideal, D.map_radical_ideal_germ, hspan,
    Ideal.radical_span_singleton_eq_span_radical ha.isLeftRegular.ne_zero]

end AlgebraicGeometry.Scheme.IdealSheafData
