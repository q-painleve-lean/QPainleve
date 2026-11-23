/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Primitive generators of fan rays

Each ray of a fan has a canonical primitive lattice generator, obtained from the
primitive generator of its own one-dimensional cone. Subdivision preserves these ray cones.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

/-- The generator of a fan ray as a primitive lattice vector. -/
def Ray.primitiveGenerator (ρ : Φ.Ray) : N :=
  TauCeti.Toric.primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property)
    (Ray.toToricRay Φ ρ ρ.toCone le_rfl)

/-- The primitive generator of a fan ray is the primitive generator in its ray cone. -/
theorem Ray.primitiveGenerator_def (ρ : Φ.Ray) :
    ρ.primitiveGenerator =
      TauCeti.Toric.primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) := (rfl)

/-- A fan ray is the cone spanned by its primitive generator. -/
theorem Ray.toCone_eq_hull_primitiveGenerator (ρ : Φ.Ray) :
    ρ.toCone.val = PointedCone.hull ℝ {i (Ray.primitiveGenerator ρ)} := by
  classical
  let σ := ρ.toCone
  let r := Ray.toToricRay Φ ρ σ le_rfl
  let hσ := Φ.isToricCone σ.property
  have hr : r.toPointedCone = σ.val := Ray.toPointedCone_toToricRay Φ ρ σ le_rfl
  have hne : i (TauCeti.Toric.primitiveGenerator Φ.lattice hσ r) ≠ 0 := by
    rw [map_ne_zero_iff _ Φ.lattice.injective]
    exact primitiveGenerator_ne_zero Φ.lattice hσ r
  exact hr ▸ r.eq_hull_singleton (hσ.salient.anti r.val.isFaceOf.le)
    (primitiveGenerator_mem Φ.lattice hσ r) hne

/-- The canonical primitive generator, using the toric ray of the ray cone itself. -/
theorem Ray.isPrimitiveGenerator (ρ : Φ.Ray) :
    IsPrimitiveGenerator i (ρ.toToricRay Φ ρ.toCone le_rfl) ρ.primitiveGenerator :=
  isPrimitiveGenerator_primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property) _

/-- A fan ray has a nonzero primitive generator. -/
@[simp]
theorem Ray.primitiveGenerator_ne_zero (ρ : Φ.Ray) : ρ.primitiveGenerator ≠ 0 :=
  ρ.isPrimitiveGenerator.ne_zero

/-- The primitive generator belongs to its ray in the ambient real vector space. -/
theorem Ray.primitiveGenerator_mem (ρ : Φ.Ray) : i ρ.primitiveGenerator ∈ ρ.toCone.val := by
  rw [← Ray.toPointedCone_toToricRay Φ ρ ρ.toCone le_rfl]
  exact ρ.isPrimitiveGenerator.mem

/-- Containment of a fan ray in a cone is detected by its primitive generator. -/
theorem Ray.toCone_le_iff (ρ : Φ.Ray) (σ : Φ.cones) :
    ρ.toCone ≤ σ ↔ i ρ.primitiveGenerator ∈ σ.val := by
  rw [← Subtype.coe_le_coe, ρ.toCone_eq_hull_primitiveGenerator, Submodule.span_le,
    Set.singleton_subset_iff]
  rfl

/-- A subdivision retains every ray of the original fan. -/
theorem IsSubdivision.ray_mem (h : Ψ.IsSubdivision Φ) (ρ : Φ.Ray) :
    ρ.toCone.val ∈ Ψ.cones := by
  let x := i ρ.primitiveGenerator
  have hx : x ∈ Φ.support := Φ.subset_support ρ.toCone.property ρ.primitiveGenerator_mem
  obtain ⟨σ, hσ, hxσ⟩ := Ψ.mem_support.mp (h.support_eq.symm ▸ hx)
  obtain ⟨τ, hτ, hστ⟩ := h.exists_cone_le hσ
  have hρσ : ρ.toCone.val ≤ σ := by
    rw [ρ.toCone_eq_hull_primitiveGenerator, Submodule.span_singleton_le_iff_mem]
    exact hxσ
  have hface := (Φ.isFaceOf_of_le hτ ρ.toCone.property (hρσ.trans hστ)).inf
    (PointedCone.IsFaceOf.refl σ)
  rw [inf_eq_right.mpr hστ, inf_eq_left.mpr hρσ] at hface
  exact Ψ.mem_of_isFaceOf hσ hface

/-- A primitive lattice vector lying in a ray is its canonical generator. -/
theorem Ray.primitiveGenerator_eq_of_mem_of_isPrimitive (ρ : Φ.Ray) {v : N}
    (hm : i v ∈ ρ.toCone.val) (hp : IsPrimitive v) : ρ.primitiveGenerator = v := by
  have hv : IsPrimitiveGenerator i (ρ.toToricRay Φ ρ.toCone le_rfl) v := by
    apply isPrimitiveGenerator_iff.mpr
    refine ⟨?_, hp⟩
    -- Express toric ray membership in its underlying pointed cone.
    change i v ∈ (ρ.toToricRay Φ ρ.toCone le_rfl).toPointedCone
    rwa [Ray.toPointedCone_toToricRay]
  exact (hv.eq_primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property)).symm

/-- An old ray, viewed as a ray of the subdividing fan. Its underlying cone is definitionally
the original cone, so the two affine charts share a coordinate ring. -/
@[expose] def IsSubdivision.liftRay (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) : Φ.Ray :=
  ⟨⟨ρ.toCone.val, h.ray_mem ρ⟩, ρ.property⟩

/-- The ray of the subdivision is the same cone. -/
@[simp]
theorem IsSubdivision.liftRay_toCone (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) :
    (h.liftRay ρ).toCone.val = ρ.toCone.val := (rfl)

/-- Subdivision preserves the primitive generator of each old ray. -/
@[simp]
theorem IsSubdivision.primitiveGenerator_liftRay (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) :
    (h.liftRay ρ).primitiveGenerator = ρ.primitiveGenerator := by
  apply Ray.primitiveGenerator_eq_of_mem_of_isPrimitive
  · rw [liftRay_toCone]
    exact ρ.primitiveGenerator_mem
  · exact ρ.isPrimitiveGenerator.isPrimitive

/-- The cone generated by the canonical primitive generator belongs to the fan. -/
theorem Ray.hull_primitiveGenerator_mem (ρ : Φ.Ray) :
    PointedCone.hull ℝ {i ρ.primitiveGenerator} ∈ Φ.cones :=
  ρ.toCone_eq_hull_primitiveGenerator ▸ ρ.toCone.property

/-- The ray of a fan generated by a primitive lattice vector. -/
def Ray.ofPrimitiveGenerator {v : N} (hv : IsPrimitive v)
    (h : PointedCone.hull ℝ {i v} ∈ Φ.cones) : Φ.Ray :=
  ⟨⟨_, h⟩, PointedCone.finrank_span_coe_hull_singleton
    (map_ne_zero_iff _ Φ.lattice.injective |>.mpr hv.ne_zero)⟩

/-- The cone underlying the ray constructed from a primitive vector is its ray hull. -/
@[simp]
theorem Ray.ofPrimitiveGenerator_toCone {v : N} (hv : IsPrimitive v)
    (h : PointedCone.hull ℝ {i v} ∈ Φ.cones) :
    (Ray.ofPrimitiveGenerator hv h).toCone.val = PointedCone.hull ℝ {i v} := (rfl)

/-- The ray constructed from a primitive vector has that vector as its generator. -/
@[simp]
theorem Ray.primitiveGenerator_ofPrimitiveGenerator {v : N} (hv : IsPrimitive v)
    (h : PointedCone.hull ℝ {i v} ∈ Φ.cones) :
    (Ray.ofPrimitiveGenerator hv h).primitiveGenerator = v :=
  (Ray.ofPrimitiveGenerator hv h).primitiveGenerator_eq_of_mem_of_isPrimitive
    (PointedCone.subset_hull (Set.mem_singleton _)) hv

/-- The primitive generator determines a fan ray. -/
theorem Ray.primitiveGenerator_injective : Function.Injective (Ray.primitiveGenerator (Φ := Φ)) :=
  fun ρ τ h ↦ by
    apply Subtype.ext
    apply Subtype.ext
    rw [Ray.toCone_eq_hull_primitiveGenerator ρ, Ray.toCone_eq_hull_primitiveGenerator τ, h]

/-- Viewing a cone ray as a fan ray preserves its primitive lattice generator. -/
@[simp]
theorem Ray.primitiveGenerator_ofToricRay (σ : Φ.cones) (ρ : ToricRay σ.val) :
    (Ray.ofToricRay Φ σ ρ).primitiveGenerator =
      TauCeti.Toric.primitiveGenerator Φ.lattice (Φ.isToricCone σ.property) ρ := by
  let τ := (Ray.ofToricRay Φ σ ρ).toCone
  let hface := Φ.isFaceOf_of_le σ.property τ.property (Ray.toCone_ofToricRay_le Φ σ ρ)
  let r := Ray.toToricRay Φ (Ray.ofToricRay Φ σ ρ) τ le_rfl
  have hr : ToricRay.faceEmbedding hface r = ρ := by
    apply SetLike.coe_injective
    exact congrArg (fun C : PointedCone ℝ V ↦ (C : Set V)) <| by
      rw [ToricRay.toPointedCone_faceEmbedding, Ray.toPointedCone_toToricRay,
        Ray.toCone_ofToricRay]
  rw [Ray.primitiveGenerator_def]
  exact (primitiveGenerator_faceEmbedding Φ.lattice (Φ.isToricCone σ.property) hface r).symm.trans
    (congrArg (TauCeti.Toric.primitiveGenerator Φ.lattice (Φ.isToricCone σ.property)) hr)

/-- The primitive generator of a fan ray agrees with its generator in every containing cone. -/
@[simp]
theorem Ray.primitiveGenerator_toToricRay (ρ : Φ.Ray) (σ : Φ.cones) (h : ρ.toCone ≤ σ) :
    Toric.primitiveGenerator Φ.lattice (Φ.isToricCone σ.property)
      (ρ.toToricRay Φ σ h) = ρ.primitiveGenerator := by
  have he := congrArg (fun s : {r : Φ.Ray // r.toCone ≤ σ} ↦ s.val.primitiveGenerator)
    ((Φ.rayEquiv σ).symm_apply_apply ⟨ρ, h⟩)
  simpa only [rayEquiv_apply, rayEquiv_symm_apply, Ray.primitiveGenerator_ofToricRay] using he

/-- On a complete fan, a lattice character nonnegative on every primitive ray
generator is zero. -/
theorem character_eq_zero_of_nonneg_primitiveGenerator (Φ : Fan i) (hc : Φ.IsComplete) (m : N →+ ℤ)
    (hm : ∀ ρ : Φ.Ray, 0 ≤ m ρ.primitiveGenerator) : m = 0 := by
  have hcone (σ : Φ.cones) : m ∈ dualSemigroup Φ.lattice σ.val := by
    let hσ := Φ.isToricCone σ.property
    apply (mem_dualSemigroup_iff_primitiveGenerator Φ.lattice hσ m).2
    intro ρ
    simpa only [Ray.primitiveGenerator_ofToricRay] using hm (Ray.ofToricRay Φ σ ρ)
  ext x
  obtain ⟨σ, hσ, hx⟩ := (Φ.isComplete_iff.1 hc) (-i x)
  have h := (mem_dualSemigroup Φ.lattice m).1 (hcone ⟨σ, hσ⟩) hx
  obtain ⟨τ, hτ, hx'⟩ := (Φ.isComplete_iff.1 hc) (i x)
  have h' := (mem_dualSemigroup Φ.lattice m).1 (hcone ⟨τ, hτ⟩) hx'
  simp only [map_neg, IsIntegralLattice.realCharacter_apply, Left.nonneg_neg_iff] at h h'
  exact_mod_cast le_antisymm h h'

open PointedCone in
/-- The ray generated by an extending basis vector at a ray index belongs to the fan. -/
theorem hull_basisVector_mem (Φ : Fan i) {σ : PointedCone ℝ V} {n : ℕ}
    (hσ : σ ∈ Φ.cones) (b : Module.Basis (Fin n) ℤ N)
    (r : ToricRay σ ↪ Fin n) (hb : IsExtendingBasis i b r) {j : Fin n}
    (hj : j ∈ Set.range r) : hull ℝ {i (b j)} ∈ Φ.cones := by
  obtain ⟨ρ, rfl⟩ := hj
  have h := hb.isPrimitiveGenerator_apply ρ
  rw [← ρ.eq_hull_singleton ((Φ.isToricCone hσ).salient.anti ρ.val.isFaceOf.le)
    h.mem (map_ne_zero_iff _ Φ.lattice.injective |>.mpr h.ne_zero)]
  exact Φ.mem_of_isFaceOf hσ ρ.val.isFaceOf

open PointedCone in
/-- Positive natural multiples of a lattice vector generate the same ray in the fan. -/
theorem hull_nsmul_mem_cones {u : N} (h : hull ℝ {i u} ∈ Φ.cones)
    {a : ℕ} (ha : 0 < a) : hull ℝ {i (a • u)} ∈ Φ.cones := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]
  have he : hull ℝ {(a : ℝ) • i u} = hull ℝ {i u} := by
    apply le_antisymm <;> rw [Submodule.span_singleton_le_iff_mem]
    · exact (smul_mem_iff _ ha').mpr (subset_hull rfl)
    · exact (smul_mem_iff _ ha').mp (subset_hull rfl)
  rwa [he]

open PointedCone in
/-- Each basis vector spans a ray in a fan containing the cone spanned by the basis. -/
theorem hull_basis_ray_mem (Φ : Fan i) {κ : Type*} (b : Module.Basis κ ℤ N)
    (hcone : hull ℝ (Set.range (i ∘ b)) ∈ Φ.cones) (j : κ) :
    hull ℝ {i (b j)} ∈ Φ.cones := by
  apply Φ.mem_of_isFaceOf hcone
  simpa only [Set.image_singleton, Function.comp_def] using
    isFaceOf_hull_image (Φ.lattice.linearIndependent_basis b) rfl {j}

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanEquiv

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- A fan equivalence sends the primitive generator of a ray to that of its image ray. -/
@[simp]
theorem primitiveGenerator_rayEquiv (e : FanEquiv Φ Ψ) (ρ : Φ.Ray) :
    (e.rayEquiv ρ).primitiveGenerator = e.latticeEquiv ρ.primitiveGenerator := by
  refine (e.rayEquiv ρ).primitiveGenerator_eq_of_mem_of_isPrimitive ?_
    ((e.latticeEquiv.toIntLinearEquiv.isPrimitive_iff).2 ρ.isPrimitiveGenerator.isPrimitive)
  rw [← e.map_lattice, toCone_rayEquiv, coneEquiv_apply_coe]
  exact ⟨_, ρ.primitiveGenerator_mem, rfl⟩

end TauCeti.Toric.FanEquiv
