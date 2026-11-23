/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Closed immersions over an isomorphism locus

A closed subscheme over the isomorphism locus of a morphism descends to a closed
subscheme of the target when its image is closed.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A preimmersion composed with a morphism that is an isomorphism over its image
is a closed immersion when that image is closed in the target. -/
theorem isClosedImmersion_comp_of_range_subset_isoLocus {C X Y : Scheme}
    (i : C ⟶ X) (f : X ⟶ Y) [IsPreimmersion i]
    (hclosed : IsClosed (Set.range (i ≫ f))) (h : Set.range (i ≫ f) ⊆ f.isoLocus) :
    IsClosedImmersion (i ≫ f) := by
  let U := f.isoLocus
  have hi : Set.range i ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact f.mem_preimage.mpr (h (Set.mem_range_self x))
  let j := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι i hi
  have hj : j ≫ (f ⁻¹ᵁ U).ι = i := IsOpenImmersion.lift_fac _ _ _
  have : IsPreimmersion (j ≫ (f ⁻¹ᵁ U).ι) := hj ▸ inferInstanceAs (IsPreimmersion i)
  have : IsPreimmersion j := IsPreimmersion.of_comp j (f ⁻¹ᵁ U).ι
  have : IsIso (f ∣_ U) := f.le_isoLocus_iff.mp le_rfl
  have : IsPreimmersion (i ≫ f) := by
    rw [← hj, Category.assoc, ← morphismRestrict_ι f U, ← Category.assoc]
    infer_instance
  exact IsClosedImmersion.of_isPreimmersion _ hclosed

end AlgebraicGeometry.Scheme.Hom
