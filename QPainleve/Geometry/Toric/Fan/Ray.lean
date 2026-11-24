/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.Determinant.Dual
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision
public import TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

import Mathlib.Tactic.FinCases
import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# Primitive generators of fan rays

Each ray of a fan has a canonical primitive lattice generator, obtained from the
primitive generator of its own one-dimensional cone. In rank two, a surjective character
vanishing on the ray generates its annihilator, and the determinant pairing detects primitive
generators up to sign. Subdivision preserves the ray cones.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i}

/-- A complete fan in a lattice with a nonzero vector has a ray. -/
theorem nonempty_ray_of_isComplete (Φ : Fan i) [Nontrivial N] (hc : Φ.IsComplete) :
    Nonempty Φ.Ray := by
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hix : i x ≠ 0 := fun h ↦ hx (Φ.lattice.injective (h.trans i.map_zero.symm))
  obtain ⟨σ, hσ, hmem⟩ := Φ.isComplete_iff.mp hc (i x)
  have hne : σ ≠ ⊥ := fun h ↦ hix (by simpa [h] using hmem)
  obtain ⟨ρ, -⟩ := Φ.exists_ray_le_of_ne_bot ⟨σ, hσ⟩ hne
  exact ⟨ρ⟩

/-- The primitive generator of a fan ray is the primitive generator in its ray cone. -/
theorem Ray.primitiveGenerator_def (ρ : Φ.Ray) :
    ρ.primitiveGenerator =
      TauCeti.Toric.primitiveGenerator Φ.lattice (Φ.isToricCone ρ.toCone.property)
        (Ray.toToricRay Φ ρ ρ.toCone le_rfl) :=
  (ρ.primitiveGenerator_toToricRay ρ.toCone le_rfl).symm

/-- A fan ray is the cone spanned by its primitive generator. -/
theorem Ray.toCone_eq_hull_primitiveGenerator (ρ : Φ.Ray) :
    ρ.toCone.val = PointedCone.hull ℝ {i (Ray.primitiveGenerator ρ)} := by
  classical
  let r := ρ.toToricRay Φ ρ.toCone le_rfl
  have hr : r.toPointedCone = ρ.toCone.val := Ray.toPointedCone_toToricRay Φ ρ ρ.toCone le_rfl
  have hp : IsPrimitiveGenerator i r ρ.primitiveGenerator :=
    ρ.isPrimitiveGenerator_primitiveGenerator ρ.toCone le_rfl
  rw [← hr]
  exact r.eq_hull_singleton ((Φ.isToricCone ρ.toCone.property).salient.anti r.val.isFaceOf.le)
    hp.mem ((map_ne_zero_iff _ Φ.lattice.injective).mpr hp.ne_zero)

/-- The canonical primitive generator, using the toric ray of the ray cone itself. -/
theorem Ray.isPrimitiveGenerator (ρ : Φ.Ray) :
    IsPrimitiveGenerator i (ρ.toToricRay Φ ρ.toCone le_rfl) ρ.primitiveGenerator :=
  ρ.isPrimitiveGenerator_primitiveGenerator ρ.toCone le_rfl

/-- A fan ray has a nonzero primitive generator. -/
@[simp]
theorem Ray.primitiveGenerator_ne_zero (ρ : Φ.Ray) : ρ.primitiveGenerator ≠ 0 :=
  ρ.isPrimitiveGenerator.ne_zero

/-- A character lies in the dual semigroup of a ray exactly when it pairs nonnegatively
with the primitive generator. -/
theorem Ray.mem_rayDualSemigroup_iff (ρ : Φ.Ray) (a : N →+ ℤ) :
    a ∈ dualSemigroup Φ.lattice ρ.toCone.val ↔ 0 ≤ a ρ.primitiveGenerator := by
  rw [ρ.toCone_eq_hull_primitiveGenerator, ← Set.image_singleton,
    mem_dualSemigroup_hull_image, Set.forall_mem_singleton]

/-- In rank two, a surjective character vanishing on a ray generates its integral annihilator. -/
theorem Ray.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero (ρ : Φ.Ray)
    (hdim : Module.finrank ℤ N = 2) {m : N →+ ℤ} (hm : m ρ.primitiveGenerator = 0)
    (hprim : Function.Surjective m) {a : N →+ ℤ} (ha : a ρ.primitiveGenerator = 0) :
    ∃ n : ℤ, n • m = a := by
  let := Φ.lattice.free
  let := Φ.lattice.finite
  obtain ⟨k, b, j, hj⟩ := ρ.isPrimitiveGenerator.isPrimitive.exists_basis
  have hk : k = 2 := by simpa using (Module.finrank_eq_card_basis b).symm.trans hdim
  subst k
  let c := b.reindex (Equiv.swap j 0)
  have hc : c 0 = ρ.primitiveGenerator := by
    simpa [c, Module.Basis.reindex_apply] using hj
  have heval (f : N →+ ℤ) (hf : f ρ.primitiveGenerator = 0) (x : N) :
      f x = c.repr x 1 * f (c 1) := by
    conv_lhs => rw [← c.sum_repr x]
    rw [map_sum, Fin.sum_univ_two]
    simp [hc, hf]
  obtain ⟨x, hx⟩ := hprim 1
  have hmul : c.repr x 1 * m (c 1) = 1 := (heval m hm x).symm.trans hx
  refine ⟨a x, AddMonoidHom.toIntLinearMap_injective (c.ext fun l ↦ ?_)⟩
  fin_cases l
  · simp [hc, ha, hm]
  · change a x * m (c 1) = a (c 1)
    rw [heval a ha x, mul_right_comm, hmul, one_mul]

/-- A primitive vector with determinant pairing zero against the ray generator is the generator
or its negative. -/
theorem Ray.eq_or_eq_neg_of_detCharacter_eq_zero (ρ : Φ.Ray) (b : Module.Basis (Fin 2) ℤ N)
    {v : N} (hprim : IsPrimitive v) (h : b.detDualEquiv v ρ.primitiveGenerator = 0) :
    v = ρ.primitiveGenerator ∨ v = -ρ.primitiveGenerator := by
  let u := ρ.primitiveGenerator
  obtain ⟨n, hn⟩ := ρ.exists_zsmul_eq_of_apply_primitiveGenerator_eq_zero
    (by simpa using Module.finrank_eq_card_basis b) (m := (b.detDualEquiv u).toAddMonoidHom)
    (a := (b.detDualEquiv v).toAddMonoidHom) (b.detDualEquiv_self u)
    (b.surjective_detDualEquiv_of_isPrimitive ρ.isPrimitiveGenerator.isPrimitive) h
  have hvn : n • u = v := by
    apply b.detDualEquiv.injective
    ext x
    simpa only [map_zsmul, LinearMap.smul_apply, AddMonoidHom.zsmul_apply,
      LinearMap.toAddMonoidHom_coe] using DFunLike.congr_fun hn x
  obtain ⟨f, hf⟩ := isPrimitive_def.mp hprim
  have hunit : IsUnit n :=
    isUnit_iff_dvd_one.mpr ⟨f u, by simpa [← hvn] using hf.symm⟩
  rcases Int.isUnit_iff.mp hunit with hn | hn
  · exact Or.inl (by simpa [u, hn] using hvn.symm)
  · exact Or.inr (by simpa [u, hn] using hvn.symm)

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
    (hm : i v ∈ ρ.toCone.val) (hp : IsPrimitive v) : ρ.primitiveGenerator = v :=
  ρ.primitiveGenerator_eq_iff.mpr ⟨hm, hp⟩

/-- An old ray, viewed as a ray of the subdividing fan. Its underlying cone is definitionally
the original cone, so the two affine charts share a coordinate ring. -/
@[expose] def IsSubdivision.liftRay (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) : Φ.Ray :=
  ⟨⟨ρ.toCone.val, h.ray_mem ρ⟩, ρ.property⟩

/-- The ray of the subdivision is the same cone. -/
@[simp]
theorem IsSubdivision.liftRay_toCone (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) :
    (h.liftRay ρ).toCone.val = ρ.toCone.val := (rfl)

/-- The old ray in its own cone chart is unchanged under subdivision. -/
theorem IsSubdivision.liftRay_toToricRay (h : Φ.IsSubdivision Ψ) (ρ : Ψ.Ray) :
    (h.liftRay ρ).toToricRay Φ (h.liftRay ρ).toCone le_rfl =
      ρ.toToricRay Ψ ρ.toCone le_rfl := by
  apply ToricRay.eq_of_toPointedCone_le (Ψ.isToricCone ρ.toCone.property).salient
  rw [Ray.toPointedCone_toToricRay, Ray.toPointedCone_toToricRay, liftRay_toCone]

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

/-- A ray contained in the hull of a primitive vector has that vector as its generator. -/
theorem Ray.primitiveGenerator_eq_of_toCone_le_hull (ρ : Φ.Ray) {σ : Φ.cones} {v : N}
    (hσ : σ.val = PointedCone.hull ℝ {i v}) (hv : IsPrimitive v) (hle : ρ.toCone ≤ σ) :
    ρ.primitiveGenerator = v := by
  have hf := Φ.isFaceOf_of_le σ.property ρ.toCone.property hle
  rw [hσ] at hf
  rcases hf.eq_bot_or_eq_of_hull_singleton (i v) with hz | he
  · exact (ρ.primitiveGenerator_ne_zero (Φ.lattice.injective (by
      simpa [hz] using ρ.primitiveGenerator_mem))).elim
  · exact ρ.primitiveGenerator_eq_of_mem_of_isPrimitive
      (he.symm ▸ PointedCone.subset_hull (Set.mem_singleton _)) hv

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
theorem Ray.primitiveGenerator_injective : Function.Injective (Ray.primitiveGenerator (Phi := Φ)) :=
  fun ρ τ h ↦ by
    apply Subtype.ext
    apply Subtype.ext
    rw [Ray.toCone_eq_hull_primitiveGenerator ρ, Ray.toCone_eq_hull_primitiveGenerator τ, h]

/-- Lifting along the identity subdivision fixes the ray. -/
@[simp]
theorem IsSubdivision.liftRay_refl (ρ : Φ.Ray) :
    (IsSubdivision.refl Φ).liftRay ρ = ρ :=
  Ray.primitiveGenerator_injective ((IsSubdivision.refl Φ).primitiveGenerator_liftRay ρ)

/-- Lifting along a composite subdivision lifts through both fans in order. -/
theorem IsSubdivision.liftRay_trans {Ω : Fan i} (h : Φ.IsSubdivision Ψ)
    (g : Ψ.IsSubdivision Ω) (ρ : Ω.Ray) :
    (h.trans g).liftRay ρ = h.liftRay (g.liftRay ρ) :=
  Ray.primitiveGenerator_injective (by simp only [IsSubdivision.primitiveGenerator_liftRay])

/-- Labelled rays with matching primitive generators lift to the same rays on a
common subdivision. -/
theorem IsSubdivision.liftRay_comp_eq_of_primitiveGenerator_eq {Ω : Fan i} {ι : Type*}
    (hΦ : Ω.IsSubdivision Φ) (hΨ : Ω.IsSubdivision Ψ)
    (ρ : ι → Φ.Ray) (τ : ι → Ψ.Ray)
    (h : ∀ j, (ρ j).primitiveGenerator = (τ j).primitiveGenerator) :
    hΦ.liftRay ∘ ρ = hΨ.liftRay ∘ τ := by
  funext j
  apply Ray.primitiveGenerator_injective
  simpa only [Function.comp_apply, IsSubdivision.primitiveGenerator_liftRay] using h j

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
