/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Pullback of Cartier divisors along isomorphisms near the support

A morphism that is an isomorphism over the support of an effective Cartier divisor
pulls it back to an effective Cartier divisor. This is the local form of Cartier
pullback used when comparing blowups under modifications away from their centers.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- Pullback preserves an effective Cartier divisor when the morphism is an isomorphism
over its support. -/
theorem IsEffectiveCartier.comap_of_support_subset_isoLocus {X Y : Scheme.{u}}
    {I : Y.IdealSheafData} (hI : I.IsEffectiveCartier) (f : X ⟶ Y)
    (h : (I.support : Set Y) ⊆ f.isoLocus) :
    (I.comap f).IsEffectiveCartier := by
  apply isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  by_cases hx : f x ∈ I.support
  · let U := f.isoLocus
    let V := f ⁻¹ᵁ U
    have : IsIso (f ∣_ U) := inferInstanceAs (IsIso (f ∣_ f.isoLocus))
    refine ⟨_, V.ι, inferInstance, ⟨⟨x, h hx⟩, rfl⟩, ?_⟩
    rw [← comap_comp, ← morphismRestrict_ι, comap_comp]
    exact (hI.comap U.ι).comap (f ∣_ U)
  · let V := f ⁻¹ᵁ I.support.compl
    refine ⟨_, V.ι, inferInstance, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rw [← comap_comp, (I.comap_eq_top_iff _).mpr ?_]
    · exact isEffectiveCartier_top _
    · rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]

end AlgebraicGeometry.Scheme.IdealSheafData
