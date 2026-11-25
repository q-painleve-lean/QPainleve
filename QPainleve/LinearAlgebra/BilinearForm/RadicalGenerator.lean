/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.LinearAlgebra.BilinearForm.Isometry

import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Isometries fixing the radical generator of a rank-two form

When the Gram matrix in the basis `(κ, δ)` is diagonal with entries `d, 0`
and `d ≠ 0`, the stabilizer of `δ` in the integral isometry group is infinite
dihedral. The two generating reflections send `κ` to `-κ` and `-κ + δ`.
The case `d = -2` describes the stabilizer on the boundary-orthogonal lattice
of the four-vertex seed of type affine A₇′.

The construction uses Mathlib's `Module.reflection` and Tau Ceti's
`dihedralGroupMulEquiv`.
-/

public section

open LinearMap Module

namespace LinearMap.BilinForm

variable {L : Type*} [AddCommGroup L]
  (B : LinearMap.BilinForm ℤ L) (b : Basis (Fin 2) ℤ L) {d : ℤ}
  (hGram : B.toMatrix b = Matrix.diagonal ![d, 0])

local notation "κ" => b 0
local notation "δ" => b 1
local notation "G" => MulAction.stabilizer B.isometryGroup δ

include hGram in
private theorem rankTwoForm_apply (x y : L) :
    B x y = d * b.coord 0 x * b.coord 0 y := by
  calc
    B x y = Matrix.toBilin b (B.toMatrix b) x y := by rw [Matrix.toBilin_toMatrix]
    _ = d * b.coord 0 x * b.coord 0 y := by
      simp [hGram, Fin.sum_univ_two, Matrix.diagonal_apply, Basis.coord_apply, mul_comm]

@[simp]
private theorem radicalGeneratorStabilizer_smul_one (g : G) : g • δ = δ :=
  MulAction.mem_stabilizer_iff.mp g.property

private theorem radicalGeneratorStabilizer_ext {g h : G} (hκ : g • κ = h • κ) : g = h := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply b.ext
  intro i
  fin_cases i
  · exact hκ
  · exact (radicalGeneratorStabilizer_smul_one B b g).trans
      (radicalGeneratorStabilizer_smul_one B b h).symm

private theorem coord_zero_reflectionVector (l : ℤ) :
    b.coord 0 (2 • κ - l • δ) = 2 := by
  simp [Basis.coord_apply]

private noncomputable def radicalReflection
    (hGram : B.toMatrix b = Matrix.diagonal ![d, 0]) (l : ℤ) : G := by
  let e := Module.reflection (coord_zero_reflectionVector b l)
  have hcoord (x : L) : b.coord 0 (e x) = -b.coord 0 x := by
    rw [Module.reflection_apply, map_sub, map_smul, coord_zero_reflectionVector, smul_eq_mul]
    omega
  have hE : e ∈ B.isometryGroup := by
    apply mem_isometryGroup_iff.mpr
    intro x y
    simp only [rankTwoForm_apply B b hGram, hcoord, mul_assoc, neg_mul_neg]
  refine ⟨⟨e, hE⟩, MulAction.mem_stabilizer_iff.mpr ?_⟩
  -- Evaluate the underlying linear equivalence of the stabilizer element.
  change e δ = δ
  rw [Module.reflection_apply]
  simp [Basis.coord_apply]

@[simp]
private theorem radicalReflection_smul_zero (l : ℤ) :
    radicalReflection B b hGram l • κ = -κ + l • δ := by
  -- The action is evaluation of the linear reflection underlying the subtype.
  change Module.reflection (coord_zero_reflectionVector b l) κ = _
  rw [Module.reflection_apply]
  simp [Basis.coord_apply, two_smul]
  abel

private theorem radicalReflection_mul_self (l : ℤ) :
    radicalReflection B b hGram l * radicalReflection B b hGram l = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  exact Module.involutive_reflection (coord_zero_reflectionVector b l)

private theorem radicalReflection_ne_one (l : ℤ) : radicalReflection B b hGram l ≠ 1 := by
  intro h
  have hk := congrArg (fun g : G ↦ b.coord 0 (g • κ)) h
  simp [Basis.coord_apply] at hk

local notation "s" => radicalReflection B b hGram 0
local notation "t" => radicalReflection B b hGram 1

private theorem radicalReflection_mul_smul_zero : (s * t) • κ = κ + δ := by
  simp [mul_smul]

private theorem radicalReflection_mul_inv_smul_zero : (s * t)⁻¹ • κ = κ - δ := by
  have hinv (l : ℤ) : (radicalReflection B b hGram l)⁻¹ = radicalReflection B b hGram l :=
    inv_eq_of_mul_eq_one_right (radicalReflection_mul_self B b hGram l)
  simp [mul_smul, hinv, sub_eq_add_neg, add_comm]

private theorem radicalReflection_mul_zpow_smul_zero (m : ℤ) :
    (s * t) ^ m • κ = κ + m • δ := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    rw [zpow_add_one, mul_smul, radicalReflection_mul_smul_zero B b hGram, smul_add, ih,
      radicalGeneratorStabilizer_smul_one, add_smul, one_smul, add_assoc]
  | pred m ih =>
    rw [zpow_sub_one, mul_smul, radicalReflection_mul_inv_smul_zero B b hGram, smul_sub, ih,
      radicalGeneratorStabilizer_smul_one, sub_smul, one_smul, add_sub_assoc]

private theorem orderOf_radicalReflection_mul : orderOf (s * t) = 0 := by
  apply orderOf_eq_zero_iff'.mpr
  intro n hn h
  have hk := congrArg (fun g : G ↦ b.coord 1 (g • κ)) ((zpow_natCast (s * t) n).trans h)
  simp only [radicalReflection_mul_zpow_smul_zero, one_smul] at hk
  simp [Basis.coord_apply, hn.ne'] at hk

/-- An isometry fixing the second vector of a basis with Gram matrix `diag(d, 0)`,
`d ≠ 0`, sends the first vector `κ` to a unique `a • κ + l • δ`, with `a` an
integer unit and `l` an integer. -/
theorem existsUnique_radicalGeneratorStabilizer_smul_basis_zero
    (hGram : B.toMatrix b = Matrix.diagonal ![d, 0]) (hd : d ≠ 0) (g : G) :
    ∃! p : ℤˣ × ℤ, g • κ = (p.1 : ℤ) • κ + p.2 • δ := by
  have hg : B (g • κ) (g • κ) = B κ κ := (mem_isometryGroup_iff.mp g.val.property) κ κ
  rw [rankTwoForm_apply B b hGram, rankTwoForm_apply B b hGram κ κ] at hg
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same, mul_one] at hg
  have ha : b.coord 0 (g • κ) = 1 ∨ b.coord 0 (g • κ) = -1 := by
    apply sq_eq_one_iff.mp
    apply mul_left_cancel₀ hd
    simpa [pow_two, mul_assoc] using hg
  obtain ⟨a, ha⟩ : ∃ a : ℤˣ, ↑a = b.coord 0 (g • κ) := by
    rcases ha with ha | ha
    · exact ⟨1, ha.symm⟩
    · exact ⟨-1, ha.symm⟩
  have hrepr (x : L) : b.coord 0 x • κ + b.coord 1 x • δ = x := by
    simpa only [Fin.sum_univ_two, Basis.coord_apply, Basis.equivFun_apply] using b.sum_equivFun x
  refine ⟨(a, b.coord 1 (g • κ)), ?_, ?_⟩
  · simpa only [Prod.fst, Prod.snd, ha] using (hrepr (g • κ)).symm
  · intro p hp
    refine Prod.ext (Units.ext ?_) ?_
    · simpa [Basis.coord_apply, ha] using (congrArg (b.coord 0) hp).symm
    · simpa [Basis.coord_apply] using (congrArg (b.coord 1) hp).symm

private theorem closure_radicalReflections (hd : d ≠ 0) :
    Subgroup.closure ({s, t} : Set G) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨⟨a, m⟩, ha, -⟩ :=
    existsUnique_radicalGeneratorStabilizer_smul_basis_zero B b hGram hd g
  have hs : s ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have hz := zpow_mem (mul_mem hs ht) m
  rcases Int.units_eq_one_or a with rfl | rfl
  · have he : g = (s * t) ^ m :=
      radicalGeneratorStabilizer_ext B b (by simpa [radicalReflection_mul_zpow_smul_zero] using ha)
    exact he ▸ hz
  · have he : g = s * (s * t) ^ m := radicalGeneratorStabilizer_ext B b (by
      simpa [mul_smul, radicalReflection_mul_zpow_smul_zero, smul_comm] using ha)
    exact he ▸ mul_mem hs hz

include hGram in
/-- A reflection sending `κ` to `-κ + δ` and a translation sending `κ` to
`κ + δ` generate the radical generator stabilizer. -/
theorem closure_pair_eq_top_of_smul_basis_zero (hd : d ≠ 0)
    {p q : G} (hp : p • κ = -κ + δ) (hq : q • κ = κ + δ) :
    Subgroup.closure ({p, q} : Set G) = ⊤ := by
  have hp' : p = t := radicalGeneratorStabilizer_ext B b (by simpa using hp)
  have hq' : q = s * t :=
    radicalGeneratorStabilizer_ext B b (hq.trans (radicalReflection_mul_smul_zero B b hGram).symm)
  rw [hp', hq']
  have ht : t ∈ Subgroup.closure ({t, s * t} : Set G) := Subgroup.subset_closure (by simp)
  have hst : s * t ∈ Subgroup.closure ({t, s * t} : Set G) :=
    Subgroup.subset_closure (by simp)
  apply top_unique
  rw [← closure_radicalReflections B b hGram hd, Subgroup.closure_le]
  rintro a (rfl | rfl)
  · simpa [mul_assoc, radicalReflection_mul_self] using mul_mem hst ht
  · exact ht

/-- The stabilizer of `δ` in the isometry group of a form with Gram matrix
`diag(d, 0)`, `d ≠ 0`, is the infinite dihedral group. The rotation `r 1`
acts by `κ ↦ κ + δ` and the reflection `sr 0` acts by `κ ↦ -κ`. -/
noncomputable def radicalGeneratorStabilizerMulEquivDihedral
    (hGram : B.toMatrix b = Matrix.diagonal ![d, 0]) (hd : d ≠ 0) :
    DihedralGroup 0 ≃* G :=
  TauCeti.dihedralGroupMulEquiv (radicalReflection_mul_self B b hGram 0)
    (radicalReflection_mul_self B b hGram 1) (radicalReflection_ne_one B b hGram 0)
    (radicalReflection_ne_one B b hGram 1) (orderOf_radicalReflection_mul B b hGram)
    (closure_radicalReflections B b hGram hd)

/-- The rotation with parameter `m` adds `m • δ` to `κ`. -/
@[simp]
theorem radicalGeneratorStabilizerMulEquivDihedral_r_smul (hd : d ≠ 0) (m : ZMod 0) :
    radicalGeneratorStabilizerMulEquivDihedral B b hGram hd (.r m) • κ =
      κ + (ZMod.cast m : ℤ) • δ := by
  rw [radicalGeneratorStabilizerMulEquivDihedral, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_r, radicalReflection_mul_zpow_smul_zero]

/-- The reflection with parameter `m` sends `κ` to `-κ + m • δ`. -/
@[simp]
theorem radicalGeneratorStabilizerMulEquivDihedral_sr_smul (hd : d ≠ 0) (m : ZMod 0) :
    radicalGeneratorStabilizerMulEquivDihedral B b hGram hd (.sr m) • κ =
      -κ + (ZMod.cast m : ℤ) • δ := by
  rw [radicalGeneratorStabilizerMulEquivDihedral, TauCeti.dihedralGroupMulEquiv_apply,
    TauCeti.dihedralHom_sr, mul_smul, radicalReflection_mul_zpow_smul_zero]
  simp [smul_comm]

end LinearMap.BilinForm
