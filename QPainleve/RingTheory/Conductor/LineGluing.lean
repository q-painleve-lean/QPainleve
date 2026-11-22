/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct

import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Gluing trivial lines across two branches

For two ring maps `f, g : B →+* C`, the equalizer is the ring of functions with
matching branch values. A unit `a : Cˣ` specifies a fiber identification. The
corresponding line is the kernel of the difference `x ↦ f x - a * g x`. A unit
in this kernel is a basis over the equalizer. The inclusion into `B` exhibits
`B` as the base change to the branch ring.

Compatible maps of the trivial branch lines descend by multiplication. A free
line with a chosen trivialization after base change to `B` determines a unique
gluing parameter. This is the rank-one calculation for descent along the
conductor square at a split node.

## References

* The Stacks Project, *Nodal curves*, Tag 0C46.
* The Stacks Project, finite projective module patching, Tag 0D2J.
-/

public noncomputable section

namespace RingHom

variable {B C : Type*} [CommRing B] [CommRing C] (f g : B →+* C)

local notation "R" => (f.eqLocus g)

/-- The difference of the two branch evaluations after identifying their fibers via `a`.
The equalizer acts on the residue ring via the common restriction of the branch maps. -/
def gluedLineDifference (a : Cˣ) :
    letI := (g.comp (f.eqLocus g).subtype).toAlgebra
    B →ₗ[R] C :=
  letI := (g.comp (f.eqLocus g).subtype).toAlgebra
  { toFun := fun x ↦ f x - (a : C) * g x
    map_add' := fun x y ↦ by simp only [map_add, mul_add, add_sub_add_comm]
    map_smul' := fun r x ↦ by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        Algebra.algebraMap_ofSubsemiring_apply, RingHom.comp_apply, Subring.subtype_apply,
        RingHom.id_apply, map_mul, RingHom.mem_eqLocus.mp r.property, mul_sub_left_distrib,
        mul_left_comm (a : C)] }

/-- The difference map subtracts the second branch value scaled by the gluing parameter. -/
@[simp] theorem gluedLineDifference_apply (a : Cˣ) (x : B) :
    letI := (g.comp (f.eqLocus g).subtype).toAlgebra
    f.gluedLineDifference g a x = f x - (a : C) * g x :=
  (rfl)

/-- The difference map is surjective if the two branch values can be prescribed independently. -/
theorem gluedLineDifference_surjective (hs : Function.Surjective (f.prod g)) (a : Cˣ) :
    letI := (g.comp (f.eqLocus g).subtype).toAlgebra
    Function.Surjective (f.gluedLineDifference g a) := by
  intro c
  obtain ⟨x, hx⟩ := hs (c, 0)
  have hf : f x = c := congrArg Prod.fst hx
  have hg : g x = 0 := congrArg Prod.snd hx
  exact ⟨x, by simp [hf, hg]⟩

/-- The line obtained by identifying the two fibers via multiplication by `a`. -/
def gluedLine (a : Cˣ) : Submodule R B :=
  letI := (g.comp (f.eqLocus g).subtype).toAlgebra
  LinearMap.ker (f.gluedLineDifference g a)

/-- The glued line is the kernel of the difference of branch evaluations. -/
theorem gluedLine_eq_ker (a : Cˣ) :
    letI := (g.comp (f.eqLocus g).subtype).toAlgebra
    f.gluedLine g a = LinearMap.ker (f.gluedLineDifference g a) :=
  (rfl)

/-- Membership in the glued line is the prescribed equality of branch values. -/
@[simp] theorem mem_gluedLine {a : Cˣ} {x : B} :
    x ∈ f.gluedLine g a ↔ f x = (a : C) * g x := by
  simp [gluedLine_eq_ker, sub_eq_zero]

private theorem unit_mul_mem_gluedLine_iff {a : Cˣ} (u : Bˣ)
    (hu : f u = (a : C) * g u) (x : B) :
    (u : B) * x ∈ f.gluedLine g a ↔ x ∈ f.eqLocus g := by
  rw [mem_gluedLine, mem_eqLocus, map_mul, map_mul, hu, ← mul_assoc]
  exact (a.isUnit.mul (u.isUnit.map g)).mul_right_inj

/-- A unit satisfying the gluing condition identifies the equalizer with the glued line
by multiplication. -/
def gluedLineEquiv (a : Cˣ) (u : Bˣ) (hu : f u = (a : C) * g u) :
    R ≃ₗ[R] f.gluedLine g a :=
  LinearEquiv.ofBijective
    (((LinearMap.mulLeft R (u : B)).comp (Algebra.linearMap R B)).codRestrict _ fun r ↦ by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
        Algebra.linearMap_apply, Algebra.algebraMap_ofSubsemiring_apply]
      exact (f.unit_mul_mem_gluedLine_iff g u hu _).mpr r.property)
    (by
      constructor
      · intro r s h
        exact Subtype.ext ((Units.mul_right_inj u).mp (congrArg Subtype.val h))
      · intro x
        have hmul := u⁻¹.inv_mul_cancel_left (x : B)
        have hx : (↑u⁻¹ : B) * x ∈ f.eqLocus g :=
          (f.unit_mul_mem_gluedLine_iff g u hu _).mp (hmul.symm ▸ x.property)
        exact ⟨⟨(↑u⁻¹ : B) * x, hx⟩, Subtype.ext hmul⟩)

/-- In the trivialization given by a unit lift, a scalar is multiplied by that lift. -/
@[simp] theorem coe_gluedLineEquiv_apply (a : Cˣ) (u : Bˣ) (hu : f u = (a : C) * g u)
    (r : R) : (f.gluedLineEquiv g a u hu r : B) = (u : B) * (r : B) :=
  (rfl)

/-- The inverse of the unit trivialization divides a section by the chosen unit. -/
@[simp] theorem coe_gluedLineEquiv_symm_apply (a : Cˣ) (u : Bˣ) (hu : f u = (a : C) * g u)
    (x : f.gluedLine g a) : ((f.gluedLineEquiv g a u hu).symm x : B) = (↑u⁻¹ : B) * (x : B) := by
  have h := congrArg (fun y : f.gluedLine g a ↦ (y : B))
    ((f.gluedLineEquiv g a u hu).apply_symm_apply x)
  rw [coe_gluedLineEquiv_apply] at h
  rw [← h, Units.inv_mul_cancel_left]

/-- The inclusion of a glued line with a unit lift exhibits its extension to the branch ring. -/
theorem isBaseChange_subtype_gluedLine_of_unit (a : Cˣ) (u : Bˣ)
    (hu : f u = (a : C) * g u) : IsBaseChange B (f.gluedLine g a).subtype := by
  refine (IsBaseChange.iff_of_equiv_comm (f.gluedLineEquiv g a u hu)
    (u.mulLeftLinearEquiv B B) ?_).mp (IsBaseChange.linearMap R B)
  exact LinearMap.ext fun r ↦ f.coe_gluedLineEquiv_apply g a u hu r

section Residues

variable (hs : Function.Surjective (f.prod g)) [IsLocalHom (f.prod g)]

include hs in
private theorem exists_unit_lift_prod (a : Cˣ) :
    ∃ u : Bˣ, f u = (a : C) * g u := by
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom (f.prod g) hs inferInstance
    (MulEquiv.prodUnits.symm (a, 1))
  have hf : f u = a := congrArg (fun v : (C × C)ˣ ↦ (v : C × C).1) hu
  have hg : g u = 1 := congrArg (fun v : (C × C)ˣ ↦ (v : C × C).2) hu
  exact ⟨u, by rw [hf, hg, mul_one]⟩

include hs in
/-- If the two residue maps jointly surject and reflect units, the glued module is free
of rank one over the equalizer. -/
theorem nonempty_gluedLineEquiv (a : Cˣ) :
    Nonempty (R ≃ₗ[R] f.gluedLine g a) := by
  obtain ⟨u, hu⟩ := f.exists_unit_lift_prod g hs a
  exact ⟨f.gluedLineEquiv g a u hu⟩

include hs in
/-- For jointly surjective residue maps that reflect units, extending the glued line to the
branch ring recovers the trivial branch line via the inclusion. -/
theorem isBaseChange_subtype_gluedLine (a : Cˣ) : IsBaseChange B (f.gluedLine g a).subtype := by
  obtain ⟨u, hu⟩ := f.exists_unit_lift_prod g hs a
  exact f.isBaseChange_subtype_gluedLine_of_unit g a u hu

end Residues

/-- With a fixed trivialization over the branch ring, a free line over the equalizer is
identified with the glued line for a unique fiber identification. -/
theorem existsUnique_gluedLine_of_isBaseChange {M : Type*} [AddCommGroup M] [Module R M]
    (e : R ≃ₗ[R] M) (i : M →ₗ[R] B) (hi : IsBaseChange B i) :
    ∃! a : Cˣ, ∃ e' : M ≃ₗ[R] f.gluedLine g a,
      (f.gluedLine g a).subtype.comp e'.toLinearMap = i := by
  -- A generator over the equalizer maps to a unit in the branch trivialization.
  have h := IsBaseChange.comp_equiv e i hi
  let p := h.lift (Algebra.linearMap R B)
  have hp : p (i (e 1)) = 1 := by
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.linearMap_apply, map_one]
      using h.lift_eq (Algebra.linearMap R B) 1
  have hp' : LinearMap.mulLeft B (p 1) = p := LinearMap.ext_ring (mul_one _)
  have hp_mul : p 1 * i (e 1) = 1 := (LinearMap.congr_fun hp' (i (e 1))).trans hp
  have hu : IsUnit (i (e 1)) := isUnit_iff_exists_inv.mpr ⟨p 1, (mul_comm _ _).trans hp_mul⟩
  obtain ⟨u, hu⟩ := hu
  let a := Units.map f.toMonoidHom u / Units.map g.toMonoidHom u
  have ha : f u = (a : C) * g u :=
    congrArg Units.val (div_mul_cancel (Units.map f.toMonoidHom u)
      (Units.map g.toMonoidHom u)).symm
  refine ⟨a, ⟨e.symm.trans (f.gluedLineEquiv g a u ha), ?_⟩, ?_⟩
  · apply (LinearMap.cancel_right e.surjective).mp
    apply LinearMap.ext_ring
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply, coe_gluedLineEquiv_apply,
      Subring.coe_one, mul_one] using hu
  · rintro b ⟨d, hd⟩
    have hb : i (e 1) ∈ f.gluedLine g b := by
      rw [← LinearMap.congr_fun hd (e 1)]
      exact (d (e 1)).property
    apply Units.ext
    apply (u.isUnit.map g).mul_left_inj.mp
    exact (hu ▸ (mem_gluedLine f g).mp hb).symm.trans ha

/-- A compatible multiplier gives a map of glued lines. The condition expresses commutativity
with the two fiber identifications. -/
def gluedLineMul {a b : Cˣ} (r : B) (hr : f r * (a : C) = (b : C) * g r) :
    f.gluedLine g a →ₗ[R] f.gluedLine g b :=
  ((LinearMap.mulLeft R r).comp (f.gluedLine g a).subtype).codRestrict _ fun x ↦ by
    have hx := (mem_gluedLine f g).mp x.property
    simp only [mem_gluedLine, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.subtype_apply]
    rw [map_mul, map_mul, hx, ← mul_assoc, hr, mul_assoc]

/-- A map descended from a compatible multiplier still acts by that multiplier in `B`. -/
@[simp] theorem coe_gluedLineMul_apply {a b : Cˣ} (r : B)
    (hr : f r * (a : C) = (b : C) * g r) (x : f.gluedLine g a) :
    (f.gluedLineMul g r hr x : B) = r * (x : B) :=
  (rfl)

/-- Every map of glued lines is induced by a unique compatible multiplier in the branch ring. -/
theorem existsUnique_gluedLineMul {a b : Cˣ} (u : Bˣ) (hu : f u = (a : C) * g u)
    (φ : f.gluedLine g a →ₗ[R] f.gluedLine g b) :
    ∃! r : B, ∃ hr : f r * (a : C) = (b : C) * g r, f.gluedLineMul g r hr = φ := by
  let h := f.isBaseChange_subtype_gluedLine_of_unit g a u hu
  let ψ := h.lift ((f.gluedLine g b).subtype.comp φ)
  have hψ : LinearMap.mulLeft B (ψ 1) = ψ := LinearMap.ext_ring (mul_one _)
  have hmul (x : f.gluedLine g a) : ψ 1 * (x : B) = (φ x : B) := calc
    _ = ψ (x : B) := LinearMap.congr_fun hψ _
    _ = _ := h.lift_eq _ x
  have hcompat : f (ψ 1) * (a : C) = (b : C) * g (ψ 1) := by
    let x : f.gluedLine g a := ⟨u, (mem_gluedLine f g).mpr hu⟩
    have hx := (mem_gluedLine f g).mp (φ x).property
    rw [← hmul, map_mul, map_mul] at hx
    apply ((u.isUnit.map g).mul_left_inj).mp
    simpa only [x, hu, ← mul_assoc] using hx
  refine ⟨ψ 1, ⟨hcompat, LinearMap.ext fun x ↦ Subtype.ext (hmul x)⟩, ?_⟩
  rintro r ⟨hr, hrφ⟩
  have heq : LinearMap.mulLeft B r = ψ := h.algHom_ext _ _ fun x ↦ by
    rw [LinearMap.mulLeft_apply, Submodule.subtype_apply, ← LinearMap.congr_fun hψ (x : B),
      LinearMap.mulLeft_apply]
    simpa only [← hmul, coe_gluedLineMul_apply] using
      congrArg (fun y : f.gluedLine g b ↦ (y : B)) (LinearMap.congr_fun hrφ x)
  simpa using LinearMap.congr_fun heq 1

end RingHom
