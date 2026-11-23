/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

import TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme

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

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ)
  {σ : PointedCone ℝ V} (hΦ : σ ∈ Φ.cones) (hΨ : σ ∈ Ψ.cones)

include hΦ hΨ in
private theorem preimageCones_faces :
    h.toFanHom.preimageCones {τ | τ.IsFaceOf σ} = {τ | τ.IsFaceOf σ} := by
  ext τ
  constructor
  · intro ht
    have htΦ := h.toFanHom.preimageCones_subset _ ht
    have hface := (h.toFanHom.mem_preimageCones_iff _ htΦ).mp ht
    exact Φ.isFaceOf_of_le hΦ htΦ ((h.le_leastCone htΦ).trans hface.le)
  · intro ht
    have htΦ := Φ.mem_of_isFaceOf hΦ ht
    have htΨ := Ψ.mem_of_isFaceOf hΨ ht
    apply (h.toFanHom.mem_preimageCones_iff _ htΦ).mpr
    rwa [h.leastCone_eq_self htΦ htΨ]

private theorem range_subfanInclusion_faces (A : Fan i) (hσ : σ ∈ A.cones)
    (S : Set (PointedCone ℝ V)) (hS : S ⊆ A.cones)
    (hf : ∀ ⦃τ ρ⦄, τ ∈ S → ρ.IsFaceOf τ → ρ ∈ S) (hfaces : S = {τ | τ.IsFaceOf σ}) :
    Set.range (A.subfanInclusion S hS hf).algebraicMap =
      Set.range (A.affineToricChartι ⟨σ, hσ⟩) := by
  subst S
  rw [A.range_subfanInclusion_algebraicMap]
  refine le_antisymm (iSup_le fun τ ↦ ?_) (le_iSup_of_le ⟨σ, ?_⟩ le_rfl)
  · have hface : τ.val.IsFaceOf σ := by
      simpa only [subfan_cones, Set.mem_ofPred_eq] using τ.property
    rw [← A.faceAffineToricSchemeMap_comp_affineToricChartι
      (τ := ⟨τ.val, hS (by simpa only [subfan_cones] using τ.property)⟩)
      (σ := ⟨σ, hσ⟩) hface, Scheme.Hom.comp_base,
      TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · rw [subfan_cones]
    exact PointedCone.IsFaceOf.refl σ

/-- The preimage of the chart of a common cone is the chart of that cone in the subdivision. -/
theorem preimage_range_affineToricChartι :
    h.toFanHom.algebraicMap ⁻¹' Set.range (Ψ.affineToricChartι ⟨σ, hΨ⟩) =
      Set.range (Φ.affineToricChartι ⟨σ, hΦ⟩) := by
  let S : Set (PointedCone ℝ V) := {τ | τ.IsFaceOf σ}
  have hS : S ⊆ Ψ.cones := fun {_} ht ↦ Ψ.mem_of_isFaceOf hΨ ht
  have hf : ∀ ⦃τ ρ⦄, τ ∈ S → ρ.IsFaceOf τ → ρ ∈ S := fun {_ _} ht hr ↦ hr.trans ht
  rw [← range_subfanInclusion_faces Ψ hΨ S hS hf rfl,
    ← h.toFanHom.range_preimageSubfanAlgebraicMap S hS hf]
  exact range_subfanInclusion_faces Φ hΦ _ _ _ (h.preimageCones_faces hΦ hΨ)

/-- On the charts of a common cone the subdivision morphism is induced by the identity. -/
@[reassoc]
theorem affineToricChartι_comp_algebraicMap :
    Φ.affineToricChartι ⟨σ, hΦ⟩ ≫ h.toFanHom.algebraicMap = Ψ.affineToricChartι ⟨σ, hΨ⟩ := by
  have hmaps : Set.MapsTo h.toFanHom.realMap (σ : Set V) σ := by
    rw [h.toFanHom_realMap]
    exact Set.mapsTo_id _
  rw [h.toFanHom.affineToricChartι_comp_algebraicMap_of_mapsTo ⟨σ, hΦ⟩ ⟨σ, hΨ⟩ hmaps]
  -- The chart depends only on the common cone and lattice, so the affine map is the identity.
  simp only [h.toFanHom_latticeMap, h.toFanHom_realMap, affineToricSchemeMap_id,
    Category.id_comp]

/-- The chart of a common cone is unchanged as a scheme under base change by the subdivision. -/
theorem isPullback_affineToricChartι :
    IsPullback (Φ.affineToricChartι ⟨σ, hΦ⟩) (𝟙 _) h.toFanHom.algebraicMap
      (Ψ.affineToricChartι ⟨σ, hΨ⟩) := by
  apply (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · simpa only [Category.id_comp] using h.affineToricChartι_comp_algebraicMap hΦ hΨ
  · apply SetLike.coe_injective
    exact h.preimage_range_affineToricChartι hΦ hΨ

include hΦ in
/-- The chart of a common cone lies in the isomorphism locus of the subdivision morphism. -/
theorem range_affineToricChartι_subset_isoLocus :
    Set.range (Ψ.affineToricChartι ⟨σ, hΨ⟩) ⊆ h.toFanHom.algebraicMap.isoLocus := by
  let j := Ψ.affineToricChartι ⟨σ, hΨ⟩
  have hp := h.isPullback_affineToricChartι hΦ hΨ
  have : IsIso (hp.isoPullback.hom ≫ Limits.pullback.snd h.toFanHom.algebraicMap j) := by
    dsimp only [j]
    rw [hp.isoPullback_hom_snd]
    infer_instance
  have hi := IsIso.of_isIso_comp_left hp.isoPullback.hom
    (Limits.pullback.snd h.toFanHom.algebraicMap j)
  rw [← Scheme.Hom.coe_opensRange]
  exact h.toFanHom.algebraicMap.le_isoLocus_iff.mpr
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange _ j) |>.mpr hi)

end TauCeti.Toric.Fan.IsSubdivision
