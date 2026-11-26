/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Codex
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.LinearAlgebra.Reflection
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
import QPainleve.LinearAlgebra.Reflection
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness

/-!
# Signed action on the boundary orthogonal lattice

A signed boundary isometry acts on the orthogonal complement of the boundary by its
restriction times its sign. The total boundary class detects the sign whenever it is
nonzero and lies in the orthogonal complement. For a unimodular cycle lattice, the
reversing involution gives a reflection of the orthogonal complement in the direction
of the total boundary class.

The construction uses `TauCeti.BilinForm.IsIsometry.map_orthogonal` to obtain the
restricted equivalence via `LinearEquiv.ofSubmodules`. The negative lift is expressed
as Mathlib's `Module.reflection`.
-/

public section

open LinearMap
open scoped Pointwise RightActions

namespace QPainleve.SignedBoundaryIsometryGroup

variable {L : Type*} [AddCommGroup L] [scalar : Module ℤ L] {n : ℕ}
variable (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L)

-- The restriction uses the submodule action induced by the ambient integer module.
attribute [local instance high] Submodule.module Submodule.Quotient.module

local notation "M" => Submodule.span ℤ (Set.range D)
local notation "K" => B.orthogonal M
local notation "δ" => ∑ i, D i

private theorem map_span_eq (g : signedBoundaryIsometryGroup B D) :
    (M).map ((toIsometry B D g).val : L →ₗ[ℤ] L) = M := by
  obtain ⟨p, hp⟩ := exists_indexPerm B D g
  simp only [Submodule.map_span, LinearEquiv.coe_coe, ← Set.range_comp', funext hp]
  exact congrArg (Submodule.span ℤ) (EquivLike.range_comp D p)

private theorem map_orthogonal_eq (g : signedBoundaryIsometryGroup B D) :
    (K).map ((toIsometry B D g).val : L →ₗ[ℤ] L) = K := by
  let e := toIsometry B D g
  rw [(BilinForm.mem_isometryGroup.mp e.property).map_orthogonal e.val.surjective,
    map_span_eq B D g]

private def signedRestrictionEquiv (g : signedBoundaryIsometryGroup B D) : K ≃ₗ[ℤ] K :=
  ((toIsometry B D g).val.ofSubmodules K K (map_orthogonal_eq B D g)).trans
    (LinearEquiv.smulOfUnit (sign B D g))

private theorem coe_signedRestrictionEquiv_apply (g : signedBoundaryIsometryGroup B D) (x : K) :
    (signedRestrictionEquiv B D g x : L) = sign B D g • (toIsometry B D g).val x := by
  simp only [signedRestrictionEquiv, LinearEquiv.smulOfUnit, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_apply, LinearEquiv.ofSubmodules_apply, Units.smul_def,
    Submodule.coe_smul]
  exact int_smul_eq_zsmul ‹Module ℤ L› _ _

/-- Restriction of a signed boundary isometry to the boundary orthogonal lattice, multiplied by
its sign. The restricted isometry acts on the possibly degenerate restricted form. -/
def signedOrthogonalRestriction :
    signedBoundaryIsometryGroup B D →* (B.restrict K).isometryGroup where
  toFun g := ⟨signedRestrictionEquiv B D g, BilinForm.mem_isometryGroup_iff.mpr (fun x y ↦ by
    have he := (BilinForm.mem_isometryGroup_iff.mp (toIsometry B D g).property) x y
    rcases Int.units_eq_one_or (sign B D g) with h | h <;>
      simpa [BilinForm.restrict_apply, coe_signedRestrictionEquiv_apply, h, Units.smul_def]
        using he)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun x ↦ Subtype.ext (by
    simp only [coe_signedRestrictionEquiv_apply, map_one, one_smul]
    rfl))
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun x ↦ Subtype.ext (by
    simp [mul_apply_eq_comp, coe_signedRestrictionEquiv_apply, Units.smul_def, mul_smul]))

variable {B D}

/-- On ambient lattice vectors, the signed restriction applies the isometry and its sign. -/
@[simp]
theorem coe_signedOrthogonalRestriction_apply (g : signedBoundaryIsometryGroup B D) (x : K) :
    ((signedOrthogonalRestriction B D g).val x : L) = sign B D g • (toIsometry B D g).val x :=
  coe_signedRestrictionEquiv_apply B D g x

variable [NeZero n]

/-- On the total boundary class, the signed restriction acts by the sign. -/
@[simp]
theorem signedOrthogonalRestriction_apply_sum (g : signedBoundaryIsometryGroup B D) (hδ : δ ∈ K) :
    (signedOrthogonalRestriction B D g).val ⟨δ, hδ⟩ = sign B D g • (⟨δ, hδ⟩ : K) := by
  apply Subtype.ext
  rw [coe_signedOrthogonalRestriction_apply, toIsometry_apply_sum]
  rfl

/-- The action on the nonzero total boundary class recovers the sign from the restriction. -/
theorem sign_eq_of_signedOrthogonalRestriction_eq [IsAddTorsionFree L]
    (hδ : δ ∈ K) (hδ₀ : δ ≠ 0)
    {g h : signedBoundaryIsometryGroup B D}
    (he : signedOrthogonalRestriction B D g = signedOrthogonalRestriction B D h) :
    sign B D g = sign B D h := by
  have hδ' := congrArg (fun e : (B.restrict K).isometryGroup ↦ (e.val ⟨δ, hδ⟩ : L)) he
  apply Units.ext
  apply IsAddTorsionFree.zsmul_left_injective hδ₀
  simpa only [coe_signedOrthogonalRestriction_apply, toIsometry_apply_sum, Units.smul_def]
    using hδ'

/-- A signed isometry acting trivially on the orthogonal lattice is a rotation whenever the
total boundary class is a nonzero element of that lattice. -/
theorem ker_signedOrthogonalRestriction_le_ker_sign [IsAddTorsionFree L]
    (hδ : δ ∈ K) (hδ₀ : δ ≠ 0) :
    (signedOrthogonalRestriction B D).ker ≤ (sign B D).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [← map_one (signedOrthogonalRestriction B D)] at hg
  simpa only [map_one] using sign_eq_of_signedOrthogonalRestriction_eq hδ hδ₀ hg

variable (B D)

local notation "ρ" => signedOrthogonalRestriction B D
local notation "W" => MonoidHom.range (MonoidHom.comp ρ (rotationInclusion B D))

omit [NeZero n] in
/-- The image of the signed restriction is the union of the rotation image and its right
coset by the restriction of any negative-sign element. -/
theorem range_signedOrthogonalRestriction_eq_union (s : signedBoundaryIsometryGroup B D)
    (hs : sign B D s = -1) :
    (↑(ρ).range : Set (B.restrict K).isometryGroup) = (W : Set _) ∪ ((W : Set _) <• ρ s) := by
  let H := (sign B D).ker
  have hcover : (Set.univ : Set (signedBoundaryIsometryGroup B D)) =
      (H : Set _) ∪ ((H : Set _) <• s) := by
    ext g
    simp only [Set.mem_univ, Set.mem_union, true_iff, mem_rightCoset_iff, SetLike.mem_coe, H,
      MonoidHom.mem_ker, map_mul, map_inv, hs]
    rcases Int.units_eq_one_or (sign B D g) with hg | hg <;> simp [hg]
  have hW : ρ '' (H : Set _) = (W : Set _) := by
    have hH : H = (rotationInclusion B D).range := (range_rotationInclusion B D).symm
    rw [hH, MonoidHom.coe_range, ← Set.range_comp]
    rfl
  calc
    _ = ρ '' (Set.univ : Set (signedBoundaryIsometryGroup B D)) := by rw [Set.image_univ]; rfl
    _ = _ := by rw [hcover, Set.image_union, Set.image_op_smul_distrib, hW]

variable {B D}

/-- The two image cosets are disjoint because they act on the nonzero total class with
opposite signs. -/
theorem disjoint_rotationRange_rightCoset [IsAddTorsionFree L] (hδ : δ ∈ K) (hδ₀ : δ ≠ 0)
    (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1) :
    Disjoint (W : Set (B.restrict K).isometryGroup) ((W : Set _) <• ρ s) := by
  refine Set.disjoint_left.mpr fun e he he' ↦ ?_
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp he
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp ((mem_rightCoset_iff _).mp he')
  have hmul : ρ (rotationInclusion B D g) * (ρ s)⁻¹ = ρ (rotationInclusion B D h) := by
    simpa only [MonoidHom.comp_apply] using hh.symm
  have heq : ρ (rotationInclusion B D h * s) = ρ (rotationInclusion B D g) := by
    rw [map_mul, ← mul_inv_eq_iff_eq_mul.mp hmul]
  have hsign : sign B D s = 1 := by
    simpa only [map_mul, sign_apply, coe_rotationInclusion, one_mul] using
      sign_eq_of_signedOrthogonalRestriction_eq hδ hδ₀ heq
  exact (by decide : (-1 : ℤˣ) ≠ 1) (hs.symm.trans hsign)

variable (B D)

/-- The signed restriction of the central sign change is negation on the orthogonal lattice. -/
@[simp]
theorem signedOrthogonalRestriction_centralSign_apply (hn : n ≤ 2) (x : K) :
    (signedOrthogonalRestriction B D (centralSign B D hn)).val x = -x := by
  apply Subtype.ext
  simp [Units.smul_def]

variable {B}

/-- For a one-component cycle, a negative signed boundary isometry whose signed restriction
acts by negation is the central sign element. -/
theorem eq_centralSign_of_signedOrthogonalRestriction [Module.Free ℤ L] [Module.Finite ℤ L]
    (hSymm : B.IsSymm) (hnondeg : B.Nondegenerate)
    {d : ZMod 1 → L} (hgram : ∀ j k, B (d j) (d k) = (-2 : ℤ) * (if j = k then 1 else 0) +
      (if k = j + 1 then 1 else 0) + (if k = j - 1 then 1 else 0))
    (g : signedBoundaryIsometryGroup B d)
    (hsign : sign B d g = -1)
    (horth : ∀ x : B.orthogonal (Submodule.span ℤ (Set.range d)),
      (signedOrthogonalRestriction B d g).val x = -x) :
    g = centralSign B d (by decide) := by
  have hone (x : L) : (1 : L ≃ₗ[ℤ] L) x = x := rfl
  apply Subtype.ext
  apply Prod.ext
  · rw [coe_centralSign, ← toIsometry_apply]
    apply B.isometryGroupEquivIsometryEquiv.injective
    refine boundary_isometry_ext (D := d) hSymm hnondeg.1
      (BoundaryCycle.span_sup_orthogonal_rat hgram hSymm hnondeg) ?_ ?_
    · intro j
      obtain ⟨p, hp⟩ := exists_indexPerm B d g
      simpa only [BilinForm.coe_isometryGroupEquivIsometryEquiv,
        OneMemClass.coe_one, hone, Subsingleton.elim (p j) j] using hp j
    · intro x hx
      have heq := congrArg Subtype.val
        ((horth ⟨x, hx⟩).trans
          (signedOrthogonalRestriction_centralSign_apply B d (by decide) ⟨x, hx⟩).symm)
      simp only [coe_signedOrthogonalRestriction_apply, hsign, sign_apply, toIsometry_apply,
        coe_centralSign] at heq
      simpa only [BilinForm.coe_isometryGroupEquivIsometryEquiv,
        toIsometry_apply, OneMemClass.coe_one, hone] using smul_left_cancel (-1 : ℤˣ) heq
  · simpa only [coe_centralSign, sign_apply] using hsign

namespace CycleReversingInvolution

variable {D} (r : CycleReversingInvolution B D)

/-- The linear form of the signed reflection on the boundary orthogonal. -/
def orthogonalReflectionForm : K →ₗ[ℤ] ℤ :=
  (2 : ℤ) • (B.flip r.cutClass).comp (K).subtype

@[simp]
theorem orthogonalReflectionForm_apply (x : K) : r.orthogonalReflectionForm x =
    2 * B x r.cutClass := by
  simp [orthogonalReflectionForm]

/-- The reflecting linear form takes the total boundary class to two. -/
theorem orthogonalReflectionForm_apply_sum (hSymm : B.IsSymm) (hδ : δ ∈ K) :
    r.orthogonalReflectionForm ⟨δ, hδ⟩ = 2 := by
  classical
  have hpair : B r.cutClass δ = 1 := by simp [map_sum]
  rw [orthogonalReflectionForm_apply, hSymm.eq δ r.cutClass, hpair, mul_one]

/-- The signed restriction of the chosen boundary involution is the module reflection
along the total boundary class. -/
theorem signedOrthogonalRestriction_eq_reflection (hδ : δ ∈ K)
    (hℓ : r.orthogonalReflectionForm ⟨δ, hδ⟩ = 2) :
    (ρ r.element).val = Module.reflection hℓ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  have hnegative : ((ρ r.element).val x : L) = -(toIsometry B D r.element).val x := by
    rw [coe_signedOrthogonalRestriction_apply, sign_apply, r.sign_element]
    simp [Units.smul_def]
  rw [hnegative, toIsometry_apply, r.toIsometry_apply_orthogonal x x.property,
    neg_add_rev, neg_neg, neg_add_eq_sub, Module.reflection_apply,
    orthogonalReflectionForm_apply, Submodule.coe_sub, Submodule.coe_smul]
  exact congrArg ((x : L) - ·) (int_smul_eq_zsmul scalar _ _).symm

end CycleReversingInvolution

variable (B)

/-- In a unimodular symmetric cycle lattice with primitive characteristic total class, the
negative lift of the cycle-reversing involution restricts to the reflection
`x ↦ x - 2 B(x,f) δ`. This reflection induces the identity on the quotient by the total class. -/
theorem exists_signedOrthogonalRestriction_eq_reflection [Module.Free ℤ L] [Module.Finite ℤ L]
    [B.IsPerfPair] (hSymm : B.IsSymm)
    (hGram : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive δ) (hCharacteristic : B.IsCharacteristic δ) :
    ∃ (hδ : δ ∈ K) (f : L) (s : signedBoundaryIsometryGroup B D)
      (hℓ : ((2 : ℤ) • (B.flip f).comp (K).subtype) ⟨δ, hδ⟩ = 2),
      sign B D s = -1 ∧ s * s = 1 ∧ (ρ s).val = Module.reflection hℓ ∧
        ∀ x : K, (ℤ ∙ (⟨δ, hδ⟩ : K)).mkQ ((ρ s).val x) = (ℤ ∙ (⟨δ, hδ⟩ : K)).mkQ x := by
  have hδ := BoundaryCycle.sum_mem_orthogonal hGram hSymm
  obtain ⟨r⟩ := nonempty_cycleReversingInvolution B D hSymm hGram hPrimitive hCharacteristic
  have hℓ := r.orthogonalReflectionForm_apply_sum hSymm hδ
  have hr := r.signedOrthogonalRestriction_eq_reflection hδ hℓ
  refine ⟨hδ, r.cutClass, r.element, hℓ, by simp, r.element_mul_self, hr, ?_⟩
  intro x
  rw [hr, Module.mkQ_reflection_apply]

end QPainleve.SignedBoundaryIsometryGroup
