/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Adjacency
public import QPainleve.Geometry.Toric.Lattice

/-!
# Transport of toric fans along integral lattice equivalences

An integral lattice equivalence transports each cone by its real extension and
induces a native `FanEquiv`. This lets fans originally presented in different
lattices be compared in the same lattice. In rank two, matching a positively oriented
pair of adjacent rays also identifies the determinant pairings.
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

/-- A subfan whose support contains that of the ambient fan contains all its cones. -/
theorem cones_eq_of_subset_of_support_subset {Ψ : Fan i} (h : Φ.cones ⊆ Ψ.cones)
    (hs : Ψ.support ⊆ Φ.support) : Φ.cones = Ψ.cones := by
  classical
  refine Set.Subset.antisymm h fun σ hσ ↦ ?_
  let ht := Ψ.isToricCone hσ
  let a := ∑ ρ ∈ ToricRay.faceFinset (PointedCone.IsFaceOf.refl σ) ht.fg,
    primitiveGenerator Ψ.lattice ht ρ
  have haσ : i a ∈ σ := by
    dsimp only [a]
    rw [map_sum]
    exact Submodule.sum_mem σ fun ρ _ ↦
      ρ.val.isFaceOf.le (primitiveGenerator_mem Ψ.lattice ht ρ)
  obtain ⟨τ, hτ, ha⟩ := Φ.mem_support.mp (hs (Ψ.mem_support.mpr ⟨σ, hσ, haσ⟩))
  have hface := Ψ.inf_isFaceOf_left hσ (h hτ)
  have hle : σ ≤ τ :=
    (ht.le_of_isFaceOf_of_sum_primitiveGenerator_mem Ψ.lattice hface ⟨haσ, ha⟩).trans inf_le_right
  exact Φ.mem_of_isFaceOf hτ (Ψ.isFaceOf_of_le (h hτ) hσ hle)

/-- A complete fan contains every cone of any fan that contains all its cones. -/
theorem cones_eq_of_isComplete_of_subset {Ψ : Fan i} (hc : Φ.IsComplete)
    (h : Φ.cones ⊆ Ψ.cones) : Φ.cones = Ψ.cones :=
  Φ.cones_eq_of_subset_of_support_subset h (fun x _ ↦ Φ.mem_support.mpr (Φ.isComplete_iff.mp hc x))

/-- Transporting a complete fan along an integral equivalence gives a complete fan. -/
theorem IsComplete.mapEquiv {Φ : Fan i} (hc : Φ.IsComplete) :
    (Φ.mapEquiv hi' e).IsComplete := by
  rw [isComplete_iff]
  intro x
  obtain ⟨σ, hσ, hx⟩ := Φ.isComplete_iff.mp hc ((Φ.lattice.extendEquiv hi' e).symm x)
  exact ⟨σ.map _, ⟨σ, hσ, rfl⟩, _, hx, LinearEquiv.apply_symm_apply _ _⟩

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

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- A fan equivalence preserves the determinant pairings if a pair of adjacent rays
and their images have determinant one in the respective lattice bases. -/
theorem detDualEquiv_of_matching_adjacent_rays (f : FanEquiv Φ Ψ)
    (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N') (hΦ : Φ.IsRegular)
    {p q : Φ.Ray} {p' q' : Ψ.Ray}
    (hp : f.rayEquiv p = p') (hq : f.rayEquiv q = q')
    (h : b.detDualEquiv p.primitiveGenerator q.primitiveGenerator = 1)
    (h' : b'.detDualEquiv p'.primitiveGenerator q'.primitiveGenerator = 1)
    (hcone : ∃ σ : Φ.cones, p.toCone ≤ σ ∧ q.toCone ≤ σ) (x y : N) :
    b'.detDualEquiv (f.latticeEquiv x) (f.latticeEquiv y) = b.detDualEquiv x y := by
  have hne : p ≠ q := by
    intro he
    simp [he, Module.Basis.detDualEquiv_self, -Module.Basis.detDualEquiv_apply] at h
  obtain ⟨σ, hpσ, hqσ⟩ := hcone
  obtain ⟨a, ha, hb⟩ := Fan.exists_basis_of_ray_ne_of_le
    ((Fan.isRegular_iff.mp hΦ) _ σ.property)
    (by simpa using Module.finrank_eq_card_basis b) hne hpσ hqσ
  let E : N ≃ₗ[ℤ] N' := f.latticeEquiv.toIntLinearEquiv
  let A := a.map E
  have hA : (A : Fin 2 → N') = ![p'.primitiveGenerator, q'.primitiveGenerator] := by
    have hp' := congrArg Fan.Ray.primitiveGenerator hp
    have hq' := congrArg Fan.Ray.primitiveGenerator hq
    funext j
    fin_cases j
    · simpa [A, E, ha, FanEquiv.primitiveGenerator_rayEquiv] using hp'
    · simpa [A, E, hb, FanEquiv.primitiveGenerator_rayEquiv] using hq'
  have h₁ : b'.det A = 1 := by
    rw [hA, ← Module.Basis.detDualEquiv_apply, h']
  have h₂ : (b.map E).det A = 1 := by
    rw [Module.Basis.det_map]
    have ha' : (a : Fin 2 → N) = ![p.primitiveGenerator, q.primitiveGenerator] := by
      funext j
      fin_cases j <;> simp [ha, hb]
    simpa only [Function.comp_def, A, Module.Basis.map_apply, E.symm_apply_apply, ha',
      ← Module.Basis.detDualEquiv_apply] using h
  have hd : b'.det = (b.map E).det := by
    calc
      b'.det = A.det := by rw [b'.det.eq_smul_basis_det A, h₁, one_smul]
      _ = (b.map E).det := by rw [(b.map E).det.eq_smul_basis_det A, h₂, one_smul]
  rw [Module.Basis.detDualEquiv_apply, hd, ← Module.Basis.detDualEquiv_apply]
  exact b.detDualEquiv_map E x y

end TauCeti.Toric.FanEquiv

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (e : FanEquiv Φ Ψ)

/-- The real map of a fan equivalence sends a cone into its image cone. -/
theorem mapsTo_coneEquiv (σ : Φ.cones) :
    Set.MapsTo e.toFanHom.realMap (σ.val : Set V) (e.coneEquiv σ).val := by
  rw [coneEquiv_apply_coe, toFanHom_realMap]
  exact fun x hx ↦ PointedCone.mem_map.mpr ⟨x, hx, rfl⟩

end TauCeti.Toric.FanEquiv
