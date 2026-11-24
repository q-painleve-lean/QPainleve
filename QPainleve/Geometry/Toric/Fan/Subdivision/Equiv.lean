/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Equiv
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

/-!
# Transport of fan subdivisions

A lattice equivalence carrying the coarse fan to another fan also carries every
specified subdivision to a subdivision. The two fan equivalences commute with
the subdivision morphisms, so the same square holds on the toric schemes.
-/

public section

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ Δ : Fan i} {Ψ : Fan i'}
  (e : FanEquiv Φ Ψ) (H : Δ.IsSubdivision Φ)

local notation "Δ'" => Δ.mapEquiv Ψ.lattice e.latticeEquiv
local notation "eΔ" => Δ.mapEquivIso Ψ.lattice e.latticeEquiv

include H in
/-- Transporting the subdividing fan along a fan equivalence gives a subdivision
of its target. -/
theorem isSubdivision_mapEquiv : (Δ').IsSubdivision Ψ := by
  have hcones : (Δ').cones = PointedCone.map e.realEquiv.toLinearMap '' Δ.cones := by
    have hr := Δ.lattice.eq_extend (i' := i') (f := e.latticeEquiv.toAddMonoidHom)
      (g := (Δ.lattice.extendEquiv Ψ.lattice e.latticeEquiv).toLinearMap)
      (Δ.lattice.extendEquiv_apply_lattice Ψ.lattice e.latticeEquiv)
    rw [Fan.mapEquiv_cones, hr, e.realEquiv_toLinearMap_eq]
    congr 2
  have hle : ∀ ⦃σ⦄, σ ∈ (Δ').cones → ∃ τ ∈ Ψ.cones, σ ≤ τ := by
    rw [hcones]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, hτ, hστ⟩ := H.exists_cone_le hσ
    exact ⟨_, (e.map_mem τ).mpr hτ, Submodule.map_mono hστ⟩
  refine ⟨hle, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := (Δ').mem_support.mp hx
    obtain ⟨τ, hτ, hστ⟩ := hle hσ
    exact Ψ.subset_support hτ (hστ hxσ)
  · intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := Ψ.mem_support.mp hx
    obtain ⟨τ, hτ⟩ := e.coneEquiv.surjective ⟨σ, hσ⟩
    have he : (e.coneEquiv τ).val = σ := congrArg Subtype.val hτ
    rw [← he, coneEquiv_apply_coe, PointedCone.mem_map] at hxσ
    obtain ⟨y, hy, rfl⟩ := hxσ
    have hyΔ : y ∈ Δ.support := H.support_eq.symm ▸ Φ.subset_support τ.property hy
    obtain ⟨υ, hυ, hyυ⟩ := Δ.mem_support.mp hyΔ
    exact (Δ').subset_support (hcones.symm ▸ Set.mem_image_of_mem _ hυ)
      (PointedCone.mem_map.mpr ⟨y, hyυ, rfl⟩)

/-- The transported subdivision morphism commutes with the original one and the
two equivalences of fans. -/
theorem toFanHom_comp_subdivision :
    (e.isSubdivision_mapEquiv H).toFanHom.comp (eΔ).toFanHom =
      e.toFanHom.comp H.toFanHom := by
  apply FanHom.ext
  simp

end TauCeti.Toric.FanEquiv
