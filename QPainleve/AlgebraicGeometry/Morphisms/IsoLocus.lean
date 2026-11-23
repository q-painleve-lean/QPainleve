/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Stalks over the isomorphism locus

A morphism induces an isomorphism on the stalks at each point lying over its isomorphism locus.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The stalk map of a morphism at any point lying over its isomorphism locus is an isomorphism. -/
theorem isIso_stalkMap_of_mem_isoLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (hx : f x ∈ f.isoLocus) : IsIso (f.stalkMap x) := by
  let U := f.isoLocus
  let j := Scheme.Opens.ι (f ⁻¹ᵁ U)
  let xU : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have : IsIso (f ∣_ U) := inferInstanceAs (IsIso (f ∣_ f.isoLocus))
  have hiOpen : IsOpenImmersion ((f ∣_ U) ≫ Scheme.Opens.ι U) := inferInstance
  have hi : IsIso ((j ≫ f).stalkMap xU) := by
    rw [← morphismRestrict_ι f U]
    exact (IsOpenImmersion.iff_isIso_stalkMap.mp hiOpen).2 xU
  have : IsIso (f.stalkMap (j xU) ≫ j.stalkMap xU) :=
    (Scheme.Hom.stalkMap_comp j f xU) ▸ hi
  exact IsIso.of_isIso_comp_right (f.stalkMap (j xU)) (j.stalkMap xU)

end AlgebraicGeometry.Scheme.Hom
