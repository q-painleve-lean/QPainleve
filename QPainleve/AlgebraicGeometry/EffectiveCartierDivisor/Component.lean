/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction

/-!
# Preservation of Cartier boundary components

Fixing the generic points of the components of an effective Cartier divisor
preserves its reduced closed subscheme.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {D : X.IdealSheafData}

/-- An automorphism fixing every codimension-one point in an effective Cartier divisor
preserves the reduced divisor as a closed subscheme. -/
theorem comap_radical_eq_of_fixes_components (hD : D.IsEffectiveCartier) (e : X ≅ X)
    (he : ∀ x : CodimensionOnePoint X, (x : X) ∈ D.support → e.hom x = x) :
    D.radical.comap e.hom = D.radical := by
  have hmaps (f : X ⟶ X) (hf : ∀ x : CodimensionOnePoint X,
      (x : X) ∈ D.support → f x = x) : Set.MapsTo f (D.support : Set X) D.support := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hD.mem_support_iff_exists_codimensionOnePoint.mp hx
    apply (hpx.map f.continuous).mem_closed D.support.isClosed
    rwa [hf p hp]
  have hinv (x : CodimensionOnePoint X) (hx : (x : X) ∈ D.support) : e.inv x = x := by
    have h := congrArg e.inv (he x hx)
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id, Scheme.Hom.id_base, TopCat.coe_id, id_eq] at h
    exact h.symm
  have hs : (D.comap e.hom).support = D.support := by
    ext x
    simp only [support_comap, Closeds.coe_preimage, Set.mem_preimage]
    refine ⟨fun hx ↦ ?_, fun hx ↦ hmaps e.hom he hx⟩
    have h := hmaps e.inv hinv hx
    rwa [← Scheme.Hom.comp_apply, e.hom_inv_id, Scheme.Hom.id_base, TopCat.coe_id, id_eq] at h
  rw [← radical_comap_of_isOpenImmersion, ← vanishingIdeal_support, ← vanishingIdeal_support, hs]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
