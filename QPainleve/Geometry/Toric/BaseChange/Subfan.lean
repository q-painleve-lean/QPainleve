/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.BaseChange.FanMap
public import TauCeti.Geometry.Toric.Algebraic.Fan.Preimage
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Open subfans of toric schemes over a coefficient ring

A face-closed collection of cones gives an open subscheme of the toric scheme.
Restriction of a map of fans to a preimage subfan gives a pullback square of schemes.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

local notation "Ψ" => (Φ.subfan S hS hface)
local notation "f" => (Φ.subfanInclusion S hS hface)

/-- On each cone chart, the map of a subfan inclusion is the ambient chart inclusion. -/
theorem affineChartι_comp_subfanInclusion_finiteFanSchemeHom
    (σ : (Ψ).cones) :
    (Ψ).affineChartι R σ ≫ (f).finiteFanSchemeHom R =
      Φ.affineChartι R ⟨σ.val, hS (by simpa only [subfan_cones] using σ.property)⟩ := by
  let τ : Φ.cones := ⟨σ.val, hS (by simpa only [subfan_cones] using σ.property)⟩
  have hmaps : Set.MapsTo (f).realMap (σ.val : Set V) (τ.val : Set V) := by
    simp only [subfanInclusion_realMap, LinearMap.id_coe]
    exact Set.mapsTo_id _
  rw [FanHom.affineChartι_comp_finiteFanSchemeHom R f σ τ hmaps]
  simp only [subfanInclusion_latticeMap, subfanInclusion_realMap,
    affineChartMap_id, Category.id_comp]
  rfl

private theorem subfanInclusion_finiteFanSchemeHom_injective :
    Function.Injective ((f).finiteFanSchemeHom R) := by
  intro x y hxy
  obtain ⟨σ, a, rfl⟩ := (Ψ).exists_affineChartι_apply_eq R x
  obtain ⟨τ, b, rfl⟩ := (Ψ).exists_affineChartι_apply_eq R y
  simp only [← Scheme.Hom.comp_apply,
    affineChartι_comp_subfanInclusion_finiteFanSchemeHom] at hxy
  apply ((Ψ).affineChartι_apply_eq_affineChartι_apply_iff R a b).mpr
  let σ' : Φ.cones := ⟨σ.val, hS (by simpa only [subfan_cones] using σ.property)⟩
  let τ' : Φ.cones := ⟨τ.val, hS (by simpa only [subfan_cones] using τ.property)⟩
  obtain ⟨z, hza, hzb⟩ :=
    (Φ.affineChartι_apply_eq_affineChartι_apply_iff R (σ := σ') (τ := τ') a b).mp hxy
  exact ⟨z, hza, hzb⟩

/-- The scheme of a subfan covers the union of its affine charts in the ambient scheme. -/
theorem range_subfanInclusion_finiteFanSchemeHom :
    Set.range ((f).finiteFanSchemeHom R) =
      ⋃ σ : (Ψ).cones,
        Set.range (Φ.affineChartι R
          ⟨σ.val, hS (by simpa only [subfan_cones] using σ.property)⟩) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, z, rfl⟩ := (Ψ).exists_affineChartι_apply_eq R y
    refine Set.mem_iUnion.mpr ⟨σ, ⟨z, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, affineChartι_comp_subfanInclusion_finiteFanSchemeHom]
  · intro hx
    obtain ⟨σ, z, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(Ψ).affineChartι R σ z, ?_⟩
    rw [← Scheme.Hom.comp_apply, affineChartι_comp_subfanInclusion_finiteFanSchemeHom]

/-- The scheme of a face-closed subfan is an open subscheme of the ambient fan scheme. -/
instance isOpenImmersion_subfanInclusion_finiteFanSchemeHom :
    IsOpenImmersion ((f).finiteFanSchemeHom R) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (Φ.subfanInclusion_finiteFanSchemeHom_injective R S hS hface)
  intro x
  obtain ⟨σ, y, hy⟩ := (Ψ).exists_affineChartι_apply_eq R x
  refine ⟨_, (Ψ).affineChartι R σ, inferInstance, ⟨y, hy⟩, ?_⟩
  rw [affineChartι_comp_subfanInclusion_finiteFanSchemeHom]
  infer_instance

end TauCeti.Toric.Fan

namespace TauCeti.Toric.Fan

section Cone

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- If every cone is a face of `σ`, its chart is the entire fan scheme. -/
theorem isIso_affineChartι_of_forall_le (A : Type u) [CommRing A]
    (Φ : Fan i) (σ : Φ.cones) (hσ : ∀ τ : Φ.cones, τ ≤ σ) :
    IsIso (Φ.affineChartι A σ) := by
  have hs : Function.Surjective (Φ.affineChartι A σ) := by
    intro x
    obtain ⟨τ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq A x
    let hτ := Φ.isFaceOf_of_le σ.property τ.property (hσ τ)
    refine ⟨faceAffineChartMap A Φ.lattice hτ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Φ.faceAffineChartMap_comp_affineChartι A
      (τ := τ) (σ := σ) hτ]
  exact (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hs⟩⟩

/-- The chart of the maximal cone identifies the scheme of its face fan. -/
theorem isIso_affineChartι_ofCone (A : Type u) [CommRing A] {σ : PointedCone ℝ V}
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    IsIso ((Fan.ofCone hi hσ).affineChartι A ⟨σ, (Fan.mem_ofCone_cones hi hσ).2 (.refl σ)⟩) :=
  (Fan.ofCone hi hσ).isIso_affineChartι_of_forall_le A _ fun τ ↦
    ((Fan.mem_ofCone_cones hi hσ).mp τ.property).le

end Cone

end TauCeti.Toric.Fan

namespace TauCeti.Toric

universe u

variable (R : Type u) [CommRing R] {N N' : Type u} {V V' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}

/-- The preimage of a face chart cut out by a character is cut out by the pulled-back character. -/
theorem preimage_range_faceAffineChartMap_inf_ker {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i') (f : N →+ N') (g : V →ₗ[ℝ] V')
    (hfg : ∀ n, g (i n) = i' (f n)) (hστ : Set.MapsTo g σ τ) (hσ : σ.FG) (hτ : τ.FG)
    (m : dualSemigroup hi' τ) :
    affineChartMap R hi hi' f g hfg hστ ⁻¹'
        Set.range (faceAffineChartMap R hi'
          (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi' m).1 m.property))) =
      Set.range (faceAffineChartMap R hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi _).1
          (dualSemigroupMap hi hi' f g hfg hστ m).property))) := by
  ext x
  rw [Set.mem_preimage, range_faceAffineChartMap R hi' hτ m,
    range_faceAffineChartMap R hi hσ, affineChartMap_def, Spec.map_apply]
  change (single m (1 : R) ∉ Ideal.comap _ x.asIdeal) ↔ _
  rw [Ideal.mem_comap, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    mapDomainAlgHom_apply, mapDomain_single]
  rfl

/-- The charts of two cones intersect in the chart of their common face. -/
theorem Fan.range_affineChartι_inter (Φ : Fan i) (σ τ : Φ.cones) :
    Set.range (Φ.affineChartι R σ) ∩ Set.range (Φ.affineChartι R τ) =
      Set.range (Φ.affineChartι R (σ ⊓ τ)) := by
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    obtain ⟨w, hw, -⟩ := (Φ.affineChartι_apply_eq_affineChartι_apply_iff R y z).mp hz.symm
    exact ⟨w, by rw [← Φ.faceAffineChartMap_comp_affineChartι R
      (Φ.inf_isFaceOf_left σ.property τ.property), Scheme.Hom.comp_apply, hw]⟩
  · rintro ⟨w, rfl⟩
    constructor
    · rw [← Φ.faceAffineChartMap_comp_affineChartι R (τ := σ ⊓ τ) (σ := σ)
        (Φ.inf_isFaceOf_left σ.property τ.property), Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    · rw [← Φ.faceAffineChartMap_comp_affineChartι R (τ := σ ⊓ τ) (σ := τ)
        (Φ.inf_isFaceOf_right σ.property τ.property), Scheme.Hom.comp_apply]
      exact Set.mem_range_self _

namespace FanHom

variable {Φ : Fan i} {Ψ : Fan i'} (f : FanHom Φ Ψ)

private theorem exists_affineChartι_eq_of_finiteFanSchemeHom_mem (σ : Φ.cones)
    (y : affineChart R Φ.lattice σ.val) (τ : Ψ.cones)
    (hy : f.finiteFanSchemeHom R (Φ.affineChartι R σ y) ∈ Set.range (Ψ.affineChartι R τ)) :
    ∃ (σ' : Φ.cones) (y' : affineChart R Φ.lattice σ'.val),
      Φ.affineChartι R σ' y' = Φ.affineChartι R σ y ∧
        (f.leastCone σ'.property).IsFaceOf τ.val := by
  let υ : Ψ.cones := ⟨f.leastCone σ.property, f.leastCone_mem σ.property⟩
  have hυ := Ψ.isToricCone υ.property
  have hmaps : Set.MapsTo f.realMap (σ.val : Set V) (υ.val : Set V') :=
    fun x hx ↦ f.map_le_leastCone σ.property ⟨x, hx, rfl⟩
  let a := affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps
  obtain ⟨m, hm, hmυτ⟩ := hυ.rational.exists_mem_dualSemigroup_inf_ker_eq Ψ.lattice
    (Ψ.inf_isFaceOf_left υ.property τ.property)
  have hρ : (υ.val ⊓ PointedCone.ofSubmodule (LinearMap.ker (Ψ.lattice.realCharacter m))).IsFaceOf
      υ.val := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Ψ.lattice m).1 hm)
  have hy' : a y ∈ Set.range (faceAffineChartMap R Ψ.lattice hρ) := by
    rw [← Scheme.Hom.comp_apply, f.affineChartι_comp_finiteFanSchemeHom R σ υ hmaps,
      Scheme.Hom.comp_apply] at hy
    have hυτ : Ψ.affineChartι R υ (a y) ∈ Set.range (Ψ.affineChartι R (υ ⊓ τ)) := by
      rw [← Ψ.range_affineChartι_inter R]
      exact ⟨⟨_, rfl⟩, hy⟩
    have hinf : υ ⊓ τ = ⟨_, Ψ.mem_of_isFaceOf υ.property hρ⟩ := Subtype.ext hmυτ.symm
    rw [hinf, ← Ψ.faceAffineChartMap_comp_affineChartι R hρ] at hυτ
    obtain ⟨z, hz⟩ := hυτ
    rw [Scheme.Hom.comp_apply] at hz
    exact ⟨z, (Ψ.affineChartι R υ).isOpenEmbedding.injective hz⟩
  change y ∈ affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps ⁻¹'
    Set.range (faceAffineChartMap R Ψ.lattice hρ) at hy'
  rw [preimage_range_faceAffineChartMap_inf_ker R Φ.lattice Ψ.lattice _ _ _ hmaps
    (Φ.isToricCone σ.property).fg hυ.fg ⟨m, hm⟩] at hy'
  obtain ⟨y', hy'⟩ := hy'
  have hσ' := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup Φ.lattice _).1
    (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps
      ⟨m, hm⟩).property)
  refine ⟨⟨_, Φ.mem_of_isFaceOf σ.property hσ'⟩, y', ?_, ?_⟩
  · rw [← hy', ← Scheme.Hom.comp_apply,
      Φ.faceAffineChartMap_comp_affineChartι R (τ := ⟨_, Φ.mem_of_isFaceOf σ.property hσ'⟩)]
  have hle : f.leastCone (Φ.mem_of_isFaceOf σ.property hσ') ≤ υ.val ⊓ τ.val := by
    rw [← hmυτ]
    refine f.leastCone_le _ (Ψ.mem_of_isFaceOf υ.property hρ) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨f.mapsTo_leastCone σ.property hx.1, ?_⟩
    have hx₂ := LinearMap.mem_ker.1 hx.2
    rwa [coe_dualSemigroupMap,
      Φ.lattice.realCharacter_comp Ψ.lattice f.latticeMap f.realMap f.map_lattice] at hx₂
  exact (Ψ.isFaceOf_of_le (Ψ.inf_mem υ.property τ.property) (f.leastCone_mem _) hle).trans
    (Ψ.inf_isFaceOf_right υ.property τ.property)

end FanHom

namespace FanHom

variable (R : Type u) [CommRing R] {N N' V V' : Type u}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V] [AddCommGroup V']
  [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {Φ : Fan i} {Ψ : Fan i'} (f : FanHom Φ Ψ)

variable (S : Set (PointedCone ℝ V')) (hS : S ⊆ Ψ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

local notation "preimageInclusion" => (Φ.subfanInclusion (f.preimageCones S)
  (f.preimageCones_subset S) (f.preimageCones_closedUnderFaces S hface))
local notation "targetInclusion" => (Ψ.subfanInclusion S hS hface)

/-- The morphism of a fan map restricts to the preimage of an open subfan. -/
theorem preimageSubfan_finiteFanSchemeHom_comp :
    (preimageInclusion).finiteFanSchemeHom R ≫ f.finiteFanSchemeHom R =
      (f.restrictToPreimage S hS hface).finiteFanSchemeHom R ≫
        (targetInclusion).finiteFanSchemeHom R := by
  rw [← finiteFanSchemeHom_comp, ← finiteFanSchemeHom_comp, subfanInclusion_comp_restrictToPreimage]

/-- The scheme of the preimage subfan is the inverse image of the open subscheme of the target. -/
theorem range_preimageSubfanInclusion_finiteFanSchemeHom :
    Set.range ((preimageInclusion).finiteFanSchemeHom R) =
      f.finiteFanSchemeHom R ⁻¹' Set.range ((targetInclusion).finiteFanSchemeHom R) := by
  rw [Fan.range_subfanInclusion_finiteFanSchemeHom, Fan.range_subfanInclusion_finiteFanSchemeHom]
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨σ, y, rfl⟩
    have hσ := f.preimageSubfan_cones_subset S hface σ.property
    have hleast := (f.mem_preimageCones_iff S hσ).1 (by
      simpa only [Fan.subfan_cones] using σ.property)
    let υ : Ψ.cones := ⟨f.leastCone hσ, f.leastCone_mem hσ⟩
    have hmaps : Set.MapsTo f.realMap (σ.val : Set V) (υ.val : Set V') :=
      fun x hx ↦ f.map_le_leastCone hσ ⟨x, hx, rfl⟩
    refine ⟨⟨υ.val, by simpa only [Fan.subfan_cones] using hleast⟩,
      affineChartMap R Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice hmaps y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      f.affineChartι_comp_finiteFanSchemeHom R ⟨σ.val, hσ⟩ υ hmaps]
  · rintro ⟨τ, hx⟩
    obtain ⟨σ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq R x
    have hτ : τ.val ∈ S := by simpa only [Fan.subfan_cones] using τ.property
    obtain ⟨σ', y', hy', hσ'⟩ :=
      f.exists_affineChartι_eq_of_finiteFanSchemeHom_mem R σ y ⟨τ.val, hS hτ⟩ hx
    exact ⟨⟨σ'.val, by simpa only [Fan.subfan_cones] using
      (f.mem_preimageCones_iff S σ'.property).2 (hface hτ hσ')⟩, y', hy'⟩

/-- A restriction to an open subfan is a pullback of toric schemes. -/
theorem isPullback_preimageSubfan_finiteFanSchemeHom :
    IsPullback ((preimageInclusion).finiteFanSchemeHom R)
      ((f.restrictToPreimage S hS hface).finiteFanSchemeHom R)
      (f.finiteFanSchemeHom R) ((targetInclusion).finiteFanSchemeHom R) :=
  (IsOpenImmersion.isPullback _ _ _ _ (f.preimageSubfan_finiteFanSchemeHom_comp R S hS hface)
    (TopologicalSpace.Opens.ext
      (f.range_preimageSubfanInclusion_finiteFanSchemeHom R S hS hface).symm)).flip

end FanHom

end TauCeti.Toric

namespace TauCeti.Toric.Fan.IsSubdivision

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ Ψ : Fan i} (h : Φ.IsSubdivision Ψ) {σ : PointedCone ℝ V}
  (hΦ : σ ∈ Φ.cones) (hΨ : σ ∈ Ψ.cones)

/-- The morphism of a subdivision restricts to the identity on the chart of a common cone. -/
@[reassoc]
theorem affineChartι_comp_finiteFanSchemeHom :
    Φ.affineChartι R ⟨σ, hΦ⟩ ≫ h.toFanHom.finiteFanSchemeHom R =
      Ψ.affineChartι R ⟨σ, hΨ⟩ := by
  have hmaps : Set.MapsTo h.toFanHom.realMap (σ : Set V) σ := by
    rw [h.toFanHom_realMap]
    exact Set.mapsTo_id _
  rw [h.toFanHom.affineChartι_comp_finiteFanSchemeHom R ⟨σ, hΦ⟩ ⟨σ, hΨ⟩ hmaps]
  simp only [h.toFanHom_latticeMap, h.toFanHom_realMap, affineChartMap_id,
    Category.id_comp]

/-- The preimage of the chart of a common cone is the chart of that cone in the subdivision. -/
theorem preimage_range_affineChartι :
    h.toFanHom.finiteFanSchemeHom R ⁻¹' Set.range (Ψ.affineChartι R ⟨σ, hΨ⟩) =
      Set.range (Φ.affineChartι R ⟨σ, hΦ⟩) := by
  ext x
  constructor
  · intro hx
    obtain ⟨κ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq R x
    obtain ⟨κ', y', hy', hσ'⟩ := h.toFanHom.exists_affineChartι_eq_of_finiteFanSchemeHom_mem R
      κ y ⟨σ, hΨ⟩ hx
    have hle : κ'.val ≤ σ := by
      intro z hz
      apply hσ'.le
      have hm := h.toFanHom.mapsTo_leastCone κ'.property hz
      rwa [h.toFanHom_realMap, LinearMap.id_apply] at hm
    let hface := Φ.isFaceOf_of_le hΦ κ'.property hle
    refine ⟨faceAffineChartMap R Φ.lattice hface y', ?_⟩
    rw [← Scheme.Hom.comp_apply, Φ.faceAffineChartMap_comp_affineChartι R
      (τ := κ') (σ := ⟨σ, hΦ⟩) hface, hy']
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.affineChartι_comp_finiteFanSchemeHom R hΦ hΨ]

/-- A common cone chart of a fan and its subdivision gives a pullback square. -/
theorem isPullback_affineChartι :
    IsPullback (Φ.affineChartι R ⟨σ, hΦ⟩) (𝟙 _) (h.toFanHom.finiteFanSchemeHom R)
      (Ψ.affineChartι R ⟨σ, hΨ⟩) := by
  apply (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · simpa only [Category.id_comp] using h.affineChartι_comp_finiteFanSchemeHom R hΦ hΨ
  · apply SetLike.coe_injective
    exact h.preimage_range_affineChartι R hΦ hΨ

end TauCeti.Toric.Fan.IsSubdivision
