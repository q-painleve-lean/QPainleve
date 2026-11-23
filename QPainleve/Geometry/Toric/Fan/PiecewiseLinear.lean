/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# Images of fans under piecewise lattice isomorphisms

A bijection of the ambient space that restricts on each cone to a lattice isomorphism
transports the fan, including its face relations, support and regularity. The construction
uses `Fan.ofCones` and the existing `IsRegularCone.map_equiv` for individual cones.
The cone order isomorphism restricts to a bijection on rays. Its dimension calculation
is the cone-by-cone version of Tau Ceti's `FanEquiv.finrank_span_coneEquiv`.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (e : V ≃ V)
  (h : ∀ σ : Φ.cones, ∃ (a : V ≃ₗ[ℝ] V) (b : N ≃+ N),
      Set.EqOn a e (σ.val : Set V) ∧ ∀ n, a (i n) = i (b n))

private def piecewiseImage (σ : Φ.cones) : PointedCone ℝ V :=
  σ.val.map (h σ).choose.toLinearMap

private theorem coe_piecewiseImage (σ : Φ.cones) :
    (Φ.piecewiseImage e h σ : Set V) = e '' (σ.val : Set V) :=
  PointedCone.coe_map _ _ |>.trans (h σ).choose_spec.choose_spec.1.image_eq

private theorem piecewiseImage_eq_map_of_le {σ τ : Φ.cones} (hle : τ.val ≤ σ.val) :
    Φ.piecewiseImage e h τ = τ.val.map (h σ).choose.toLinearMap := by
  apply SetLike.coe_injective
  rw [coe_piecewiseImage, PointedCone.coe_map]
  exact ((h σ).choose_spec.choose_spec.1.mono hle).image_eq.symm

private theorem piecewiseImage_inf (σ τ : Φ.cones) :
    Φ.piecewiseImage e h (σ ⊓ τ) = Φ.piecewiseImage e h σ ⊓ Φ.piecewiseImage e h τ := by
  apply SetLike.coe_injective
  simp only [coe_piecewiseImage, Submodule.coe_inf, Fan.coe_inf]
  exact Set.image_inter e.injective

/-- Transport a fan by a bijection acting on every cone as an ambient linear equivalence
compatible with an integral lattice automorphism. -/
def mapPiecewiseLinear : Fan i :=
  Fan.ofCones Φ.lattice (Set.range (Φ.piecewiseImage e h)) (Set.finite_range _)
    (by
      rintro _ ⟨σ, rfl⟩
      exact (isToricCone_map_equiv_iff (h σ).choose_spec.choose_spec.2).mpr
        (Φ.isToricCone σ.property))
    (by
      rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
      rw [← piecewiseImage_inf, piecewiseImage_eq_map_of_le Φ e h inf_le_left]
      exact (Φ.inf_isFaceOf_left σ.property τ.property).map_equiv (h σ).choose)

/-- The cones of the transported fan are exactly the images of the original cones. -/
theorem mem_mapPiecewiseLinear_cones {τ : PointedCone ℝ V} :
    τ ∈ (Φ.mapPiecewiseLinear e h).cones ↔
      ∃ σ ∈ Φ.cones, (τ : Set V) = e '' (σ : Set V) := by
  rw [mapPiecewiseLinear, Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, hτ⟩
    let a := (h σ).choose
    let κ := τ.map a.symm.toLinearMap
    have hmap : κ.map a.toLinearMap = τ := by
      simp only [κ, PointedCone.map_map, a.comp_symm, PointedCone.map_id]
    have hκ : κ.IsFaceOf σ.val :=
      PointedCone.IsFaceOf.of_map_injective a.injective (hmap.symm ▸ hτ)
    let σ' : Φ.cones := ⟨κ, Φ.mem_of_isFaceOf σ.property hκ⟩
    refine ⟨κ, σ'.property, ?_⟩
    rw [← coe_piecewiseImage Φ e h σ', piecewiseImage_eq_map_of_le Φ e h (σ := σ) hκ.le, hmap]
  · rintro ⟨σ, hσ, hτ⟩
    let σ' : Φ.cones := ⟨σ, hσ⟩
    have hτ' : τ = Φ.piecewiseImage e h σ' :=
      SetLike.coe_injective (hτ.trans (coe_piecewiseImage Φ e h σ').symm)
    exact ⟨_, ⟨σ', rfl⟩, hτ' ▸ PointedCone.IsFaceOf.refl τ⟩

/-- Transporting a fan takes its support to the image of the original support. -/
@[simp]
theorem support_mapPiecewiseLinear : (Φ.mapPiecewiseLinear e h).support = e '' Φ.support := by
  ext x
  rw [mapPiecewiseLinear, Fan.support_ofCones, Set.mem_iUnion₂, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, hx⟩
    rw [coe_piecewiseImage] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, Φ.subset_support σ.property hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨σ, hσ, hyσ⟩ := Φ.mem_support.mp hy
    let σ' : Φ.cones := ⟨σ, hσ⟩
    refine ⟨Φ.piecewiseImage e h σ', ⟨σ', rfl⟩, ?_⟩
    rw [coe_piecewiseImage]
    exact Set.mem_image_of_mem e hyσ

/-- Transport preserves and reflects completeness. -/
theorem isComplete_mapPiecewiseLinear_iff :
    (Φ.mapPiecewiseLinear e h).IsComplete ↔ Φ.IsComplete := by
  simp only [Fan.isComplete_iff, ← Fan.mem_support, support_mapPiecewiseLinear]
  exact ⟨fun hp x ↦ by simpa using hp (e x),
    fun hp x ↦ ⟨e.symm x, hp _, e.apply_symm_apply x⟩⟩

/-- Transport preserves and reflects regularity. -/
theorem isRegular_mapPiecewiseLinear_iff : (Φ.mapPiecewiseLinear e h).IsRegular ↔ Φ.IsRegular := by
  simp only [Fan.isRegular_iff]
  constructor
  · intro hreg σ hσ
    let σ' : Φ.cones := ⟨σ, hσ⟩
    have hm : Φ.piecewiseImage e h σ' ∈ (Φ.mapPiecewiseLinear e h).cones :=
      (mem_mapPiecewiseLinear_cones Φ e h).mpr ⟨σ, hσ, coe_piecewiseImage _ _ _ σ'⟩
    exact (isRegularCone_map_equiv_iff (h σ').choose_spec.choose_spec.2).mp (hreg _ hm)
  · intro hreg τ hτ
    obtain ⟨σ, hσ, heq⟩ := (mem_mapPiecewiseLinear_cones Φ e h).mp hτ
    let σ' : Φ.cones := ⟨σ, hσ⟩
    have hτ' : τ = Φ.piecewiseImage e h σ' :=
      SetLike.coe_injective (heq.trans (coe_piecewiseImage Φ e h σ').symm)
    exact hτ'.symm ▸ (hreg _ hσ).map_equiv (h σ').choose_spec.choose_spec.2

/-- The cone poset of a piecewise lattice image is canonically isomorphic to that of the
original fan. The order is cone inclusion. -/
def mapPiecewiseLinearConeEquiv : Φ.cones ≃o (Φ.mapPiecewiseLinear e h).cones where
  toEquiv := Equiv.ofBijective (fun σ ↦ ⟨Φ.piecewiseImage e h σ,
    (Φ.mem_mapPiecewiseLinear_cones e h).mpr ⟨_, σ.property, coe_piecewiseImage Φ e h σ⟩⟩) (by
    constructor
    · intro σ τ heq
      apply Subtype.ext
      apply SetLike.coe_injective
      apply e.injective.image_injective
      rw [← coe_piecewiseImage Φ e h σ, ← coe_piecewiseImage Φ e h τ]
      exact congrArg (fun κ : (Φ.mapPiecewiseLinear e h).cones ↦ (κ.val : Set V)) heq
    · intro τ
      obtain ⟨σ, hσ, heq⟩ := (Φ.mem_mapPiecewiseLinear_cones e h).mp τ.property
      refine ⟨⟨σ, hσ⟩, Subtype.ext (SetLike.coe_injective ?_)⟩
      exact (coe_piecewiseImage Φ e h ⟨σ, hσ⟩).trans heq.symm)
  map_rel_iff' := by
    intro σ τ
    -- The order on both cone subtypes is comparison of their underlying sets.
    change (Φ.piecewiseImage e h σ : Set V) ⊆ (Φ.piecewiseImage e h τ : Set V) ↔
      (σ.val : Set V) ⊆ (τ.val : Set V)
    rw [coe_piecewiseImage, coe_piecewiseImage, Set.image_subset_image_iff e.injective]

/-- The transported cone consists of the images of the vectors of the original cone. -/
@[simp]
theorem coe_mapPiecewiseLinearConeEquiv (σ : Φ.cones) :
    ((Φ.mapPiecewiseLinearConeEquiv e h σ).val : Set V) = e '' (σ.val : Set V) :=
  coe_piecewiseImage Φ e h σ

/-- A piecewise lattice change preserves the dimension of every cone. -/
@[simp]
theorem finrank_span_mapPiecewiseLinearConeEquiv (σ : Φ.cones) :
    Module.finrank ℝ (Submodule.span ℝ ((Φ.mapPiecewiseLinearConeEquiv e h σ).val : Set V)) =
      Module.finrank ℝ (Submodule.span ℝ (σ.val : Set V)) := by
  -- Use the linear equivalence on this cone to compute the span of its image.
  change Module.finrank ℝ (Submodule.span ℝ (Φ.piecewiseImage e h σ : Set V)) = _
  rw [piecewiseImage, PointedCone.coe_map, Submodule.span_image, LinearEquiv.finrank_map_eq]

/-- A piecewise lattice change induces a bijection on the fan's rays. -/
def mapPiecewiseLinearRayEquiv : Φ.Ray ≃ (Φ.mapPiecewiseLinear e h).Ray :=
  (Φ.mapPiecewiseLinearConeEquiv e h).toEquiv.subtypeEquiv
    (fun σ ↦ by simp [finrank_span_mapPiecewiseLinearConeEquiv Φ e h σ])

/-- The ray equivalence is the restriction of the cone order isomorphism. -/
@[simp]
theorem mapPiecewiseLinearRayEquiv_toCone (ρ : Φ.Ray) :
    (Φ.mapPiecewiseLinearRayEquiv e h ρ).toCone =
      Φ.mapPiecewiseLinearConeEquiv e h ρ.toCone := (rfl)

/-- The ambient vector of the image ray's primitive generator is the image of the
original primitive generator. -/
theorem mapPiecewiseLinearRayEquiv_primitiveGenerator (ρ : Φ.Ray) :
    i (Φ.mapPiecewiseLinearRayEquiv e h ρ).primitiveGenerator = e (i ρ.primitiveGenerator) := by
  let τ := Φ.mapPiecewiseLinearRayEquiv e h ρ
  obtain ⟨a, b, ha, hb⟩ := h ρ.toCone
  have hmap : i (b ρ.primitiveGenerator) = e (i ρ.primitiveGenerator) :=
    (hb _).symm.trans (ha ρ.primitiveGenerator_mem)
  have hmem : i (b ρ.primitiveGenerator) ∈ τ.toCone.val := by
    rw [← SetLike.mem_coe, mapPiecewiseLinearRayEquiv_toCone, coe_mapPiecewiseLinearConeEquiv, hmap]
    exact Set.mem_image_of_mem e ρ.primitiveGenerator_mem
  have hp := (b.toIntLinearEquiv.isPrimitive_iff).mpr ρ.isPrimitiveGenerator.isPrimitive
  rw [τ.primitiveGenerator_eq_of_mem_of_isPrimitive hmem hp]
  exact hmap

end TauCeti.Toric.Fan
