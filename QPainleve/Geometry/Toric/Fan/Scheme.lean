/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

/-!
# Algebraic realizations of fan equivalences

The toric morphism of a fan equivalence is an isomorphism. Its point map transports
the dense torus and carries each affine chart into the chart of the image cone.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.FanEquiv

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The algebraic morphisms of a fan equivalence and its inverse compose to the identity. -/
@[reassoc (attr := simp)]
theorem algebraicMap_comp_symm :
    e.toFanHom.algebraicMap ≫ e.symm.toFanHom.algebraicMap = 𝟙 Φ.algebraicRealization := by
  rw [← FanHom.algebraicMap_comp, ← toFanHom_trans, self_trans_symm,
    toFanHom_refl, FanHom.algebraicMap_id]

/-- A fan equivalence induces an isomorphism of toric schemes. -/
instance isIso_algebraicMap : IsIso e.toFanHom.algebraicMap :=
  ⟨⟨e.symm.toFanHom.algebraicMap, e.algebraicMap_comp_symm,
    by simpa only [symm_symm] using e.symm.algebraicMap_comp_symm⟩⟩

/-- The real map of a fan equivalence sends a cone into its image cone. -/
theorem mapsTo_coneEquiv (σ : Φ.cones) :
    Set.MapsTo e.toFanHom.realMap (σ.val : Set V) (e.coneEquiv σ).val := by
  rw [coneEquiv_apply_coe, toFanHom_realMap]
  exact fun x hx ↦ PointedCone.mem_map.mpr ⟨x, hx, rfl⟩

/-- Points in a cone chart map into the chart of the image cone. -/
theorem mapsTo_affineToricChartι (σ : Φ.cones) :
    Set.MapsTo e.toFanHom.algebraicMap (Set.range (Φ.affineToricChartι σ))
      (Set.range (Ψ.affineToricChartι (e.coneEquiv σ))) := by
  rintro _ ⟨x, rfl⟩
  rw [← Scheme.Hom.comp_apply, e.toFanHom.affineToricChartι_comp_algebraicMap_of_mapsTo
    σ (e.coneEquiv σ) (e.mapsTo_coneEquiv σ), Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

private theorem mapsTo_denseTorus (h₀ : Nonempty Φ.cones) (h₁ : Nonempty Ψ.cones) :
    Set.MapsTo e.toFanHom.algebraicMap (Set.range (Φ.denseTorusι h₀))
      (Set.range (Ψ.denseTorusι h₁)) := by
  rintro _ ⟨x, rfl⟩
  rw [← Scheme.Hom.comp_apply, e.toFanHom.denseTorusι_comp_algebraicMap h₀,
    Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

/-- A point maps into the dense torus precisely when it lies in the source dense torus. -/
theorem preimage_range_denseTorusι (h₀ : Nonempty Φ.cones) (h₁ : Nonempty Ψ.cones) :
    e.toFanHom.algebraicMap ⁻¹' Set.range (Ψ.denseTorusι h₁) =
      Set.range (Φ.denseTorusι h₀) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (e.mapsTo_denseTorus h₀ h₁)
  simpa only [← Scheme.Hom.comp_apply, algebraicMap_comp_symm, Scheme.Hom.id_base,
    TopCat.coe_id, id_eq] using
    e.symm.mapsTo_denseTorus h₁ h₀ hx

end TauCeti.Toric.FanEquiv
