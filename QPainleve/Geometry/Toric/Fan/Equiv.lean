/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Lattice
public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

/-!
# Transport of toric fans along integral lattice equivalences

An integral lattice equivalence transports each cone by its real extension and
induces a native `FanEquiv`. This lets fans originally presented in different
lattices be compared in the same lattice.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  (Φ : Fan i) (hi' : IsIntegralLattice i') (e : N ≃+ N')

local notation "E" => Φ.lattice.extendEquiv hi' e
local notation "F" => LinearEquiv.toLinearMap (Φ.lattice.extendEquiv hi' e)

/-- The image fan consists of the images of the source cones under the real extension. -/
def mapEquiv : Fan i' where
  lattice := hi'
  cones := PointedCone.map F '' Φ.cones
  finite_cones := Φ.finite_cones.image _
  isToricCone := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (isToricCone_map_equiv_iff (Φ.lattice.extendEquiv_apply_lattice hi' e)).mpr
      (Φ.isToricCone hσ)
  mem_of_isFaceOf := by
    rintro _ τ ⟨σ, hσ, rfl⟩ hτ
    have hmap : (τ.map (E).symm.toLinearMap).map F = τ := by
      rw [PointedCone.map_map, LinearEquiv.comp_symm, PointedCone.map_id]
    exact ⟨τ.map (E).symm.toLinearMap, Φ.mem_of_isFaceOf hσ
      (PointedCone.IsFaceOf.of_map_injective (E).injective (hmap.symm ▸ hτ)), hmap⟩
  inf_isFaceOf_left := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    have hmap : (σ ⊓ τ).map F = σ.map F ⊓ τ.map F := by
      apply SetLike.coe_injective
      simp only [PointedCone.coe_map, Submodule.coe_inf]
      exact Set.image_inter (E).injective
    rw [← hmap]
    exact (Φ.inf_isFaceOf_left hσ hτ).map_equiv E

/-- The set of cones of the transported fan is the image of the original set of cones. -/
theorem mapEquiv_cones : (Φ.mapEquiv hi' e).cones = PointedCone.map F '' Φ.cones := (rfl)

/-- An integral equivalence induces a fan equivalence onto the transported fan. -/
def mapEquivIso : FanEquiv Φ (Φ.mapEquiv hi' e) where
  latticeEquiv := e
  realEquiv := E
  map_lattice := Φ.lattice.extendEquiv_apply_lattice hi' e
  map_mem σ := by
    rw [mapEquiv_cones]
    constructor
    · rintro ⟨τ, hτ, h⟩
      have h' := congrArg (PointedCone.map (E).symm.toLinearMap) h
      rw [PointedCone.map_map, PointedCone.map_map, LinearEquiv.symm_comp, PointedCone.map_id,
        PointedCone.map_id] at h'
      exact h' ▸ hτ
    · exact Set.mem_image_of_mem _

/-- The integral map of the image fan equivalence is the original lattice equivalence. -/
@[simp]
theorem mapEquivIso_latticeEquiv : (Φ.mapEquivIso hi' e).latticeEquiv = e := (rfl)

end TauCeti.Toric.Fan
