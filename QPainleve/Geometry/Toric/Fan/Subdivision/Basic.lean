/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.Subfan
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Affine charts preserved by subdivisions of fans

A cone that belongs to both fans has the same affine chart on either toric
scheme. The subdivision morphism is an isomorphism over this chart.
The calculation uses Tau Ceti's inverse image of an open subfan, applied to the
subfan of faces of the common cone.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  {σ : PointedCone ℝ V} (hΦ : σ ∈ Φ.cones) (hΨ : σ ∈ Ψ.cones)

include hΦ in
/-- The chart of a common cone lies in the isomorphism locus of the subdivision morphism. -/
theorem range_affineChartι_subset_isoLocus :
    Set.range (Ψ.affineChartι R ⟨σ, hΨ⟩) ⊆ (h.toFanHom.finiteFanSchemeHom R).isoLocus := by
  let j := Ψ.affineChartι R ⟨σ, hΨ⟩
  have hp := h.isPullback_affineChartι R hΦ hΨ
  have : IsIso (hp.isoPullback.hom ≫ Limits.pullback.snd (h.toFanHom.finiteFanSchemeHom R) j) := by
    dsimp only [j]
    rw [hp.isoPullback_hom_snd]
    infer_instance
  have hi := IsIso.of_isIso_comp_left hp.isoPullback.hom
    (Limits.pullback.snd (h.toFanHom.finiteFanSchemeHom R) j)
  rw [← Scheme.Hom.coe_opensRange]
  exact (h.toFanHom.finiteFanSchemeHom R).le_isoLocus_iff.mpr
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange _ j) |>.mpr hi)

end TauCeti.Toric.Fan.IsSubdivision
