/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.MarkedAction
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.PicardAction
import TauCeti.Algebra.Group.Action.Pow

/-!
# Normal forms for the doubled-square cluster modular groups

Every unsigned point map is uniquely `π₂ ^ i * T ^ m` with `0 ≤ i < 4` and `m : ℤ`.
The signed normal form appends `π₁ ^ e` with `e = 0` or `e = 1`. On the Picard lattice
the product order is reversed. The sign and orthogonal action determine all the exponents
except for the choice between two quarter-turn powers differing by the boundary half-turn.

The cluster words are those of Bershtein, Gavrylenko and Marshakov, *Cluster integrable
systems, q-Painlevé equations and their quantization*, equation (3.1), in reciprocal
coordinates. The proof uses the marked Picard comparison,
`ker_four_vertex_rotation_restriction`, and `TauCeti.zpow_smul_eq_add_zsmul`.
-/

public noncomputable section

open CategoryTheory Module MulOpposite

namespace QPainleve.FourVertex

open Cluster SignedBoundaryIsometryGroup

local notation "L" => Fin 10 → ℤ
local notation "B" => exchangeMatrix
local notation "H" => intersectionForm
local notation "D" => boundaryClass
local notation "G" => boundaryRotationGroup H D
local notation "Ĝ" => signedBoundaryIsometryGroup H D
local notation "incl" => rotationInclusion H D
local notation "res" => MonoidHom.comp (signedOrthogonalRestriction H D) incl
local notation "κ" => (boundaryOrthogonalBasis 0 : L)
local notation "δ" => (boundaryOrthogonalBasis 0 : L) + (boundaryOrthogonalBasis 1 : L)
local notation "act[" g "," x "]" => Subtype.val (Subtype.val (g : G)) (x : L)
local notation "Γ" => ClusterModularGroup ℂ B
local notation "Γ̂" => SignedClusterModularGroup ℂ B
local notation "eval[" w "]" => signedClusterModularGroupMap ℂ B (End.of w)
local notation "unsigned[" w "," h "]" =>
  clusterModularGroupMap ℂ B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h))
local notation "p" => quarterTurn
local notation "t" => picardTranslation

private theorem rotation_apply_orthogonal_sum (g : G) : act[g,δ] = δ := by
  have hδ : δ = ∑ j : ZMod 8, D j := by
    simpa only [Fin.sum_univ_two] using sum_boundaryOrthogonalBasis
  rw [hδ]
  simpa only [toIsometry_apply, coe_rotationInclusion] using toIsometry_apply_sum H D (incl g)

private theorem translation_zpow_apply (m : ℤ) : act[t ^ m, κ] = κ + m • δ := by
  have h (n : ℤ) : picardTranslation.val.val • (κ + n • δ) = κ + (n + 1) • δ := by
    rw [LinearEquiv.smul_def, map_add, map_smul, rotation_apply_orthogonal_sum,
      picardTranslation_boundaryOrthogonalBasis_zero]
    simp only [Submodule.coe_add, add_smul, one_smul]
    abel
  have hm : m • (1 : ℤ) = m := by simp
  simpa only [zero_smul, add_zero, zero_add, hm, Subgroup.coe_zpow,
    LinearEquiv.smul_def] using TauCeti.zpow_smul_eq_add_zsmul h m 0

private theorem quarterTurn_pow_apply_orthogonal (i : Fin 4) :
    act[p ^ (i : ℕ),κ] = if Even (i : ℕ) then κ else (boundaryOrthogonalBasis 1 : L) := by
  fin_cases i <;>
    simp [pow_succ', Subgroup.coe_mul, mul_apply_eq_comp, Nat.even_iff,
      -coe_boundaryOrthogonalBasis_zero, -coe_boundaryOrthogonalBasis_one]

private theorem quarterTurn_pow_apply_boundary_zero (i : Fin 4) :
    act[p ^ (i : ℕ),D 0] = D (-(2 : ZMod 8) * (i : ℕ)) := by
  fin_cases i <;> norm_num [pow_succ', Subgroup.coe_mul, mul_apply_eq_comp] <;>
    exact congrArg D (by decide)

private theorem normalFormPicard_apply (i : Fin 4) (m : ℤ) :
    act[t ^ m * p ^ (i : ℕ),κ] =
      if Even (i : ℕ) then κ + m • δ else -κ + (1 - m) • δ := by
  have h := rotation_apply_orthogonal_sum (t ^ m)
  simp only [map_add, translation_zpow_apply] at h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_apply_eq_comp, quarterTurn_pow_apply_orthogonal]
  split_ifs
  · exact translation_zpow_apply m
  · rw [eq_sub_of_add_eq' h, sub_smul, one_smul]
    abel

private theorem rotationRestriction_eq_of_apply (g h : G) (heq : act[g,κ] = act[h,κ]) :
    res g = res h := by
  have hsum := (rotation_apply_orthogonal_sum g).trans (rotation_apply_orthogonal_sum h).symm
  simp only [map_add, heq, add_right_inj] at hsum
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply boundaryOrthogonalBasis.ext
  intro j
  apply Subtype.ext
  simp only [LinearEquiv.coe_coe, MonoidHom.comp_apply, coe_signedOrthogonalRestriction_apply,
    sign_apply, coe_rotationInclusion, one_smul, toIsometry_apply]
  fin_cases j
  · exact heq
  · exact hsum

private theorem normalFormPicard_surjective :
    Function.Surjective (fun a : Fin 4 × ℤ ↦ t ^ a.2 * p ^ (a.1 : ℕ)) := by
  intro g
  -- First match the action on the orthogonal lattice using a quarter-turn exponent of 0 or 1.
  obtain ⟨⟨s, l⟩, hg, -⟩ := existsUnique_rotation_apply_boundaryOrthogonalBasis_zero g
  obtain ⟨i, m, h⟩ : ∃ (i : Fin 2) (m : ℤ),
      act[t ^ m * p ^ (i : ℕ),κ] = act[g,κ] := by
    rcases Int.units_eq_one_or s with rfl | rfl
    · refine ⟨0, l, ?_⟩
      rw [hg]
      simpa [Nat.even_iff] using normalFormPicard_apply 0 l
    · refine ⟨1, 1 - l, ?_⟩
      rw [hg]
      simpa [Nat.even_iff] using normalFormPicard_apply 1 (1 - l)
  let a := t ^ m * p ^ (i : ℕ)
  have hk : a⁻¹ * g ∈ ((res).ker : Set G) := by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      rotationRestriction_eq_of_apply a g h, inv_mul_cancel]
  rw [ker_four_vertex_rotation_restriction] at hk
  -- The possible half-turn increases the quarter-turn exponent by two.
  rcases Set.mem_insert_iff.mp hk with hk | hk
  · exact ⟨⟨i.castLE (by decide), m⟩, inv_mul_eq_one.mp hk⟩
  · have hg' := eq_mul_of_inv_mul_eq (Set.mem_singleton_iff.mp hk)
    refine ⟨⟨⟨(i : ℕ) + 2, by omega⟩, m⟩, ?_⟩
    simpa only [a, pow_add, pow_two p, quarterTurn_mul_self, ← mul_assoc] using hg'.symm

private theorem normalFormPicard_injective :
    Function.Injective (fun a : Fin 4 × ℤ ↦ t ^ a.2 * p ^ (a.1 : ℕ)) := by
  rintro ⟨i, m⟩ ⟨j, n⟩ h
  let coeff (k : Fin 4) (l : ℤ) : ℤˣ × ℤ :=
    if Even (k : ℕ) then (1, l) else (-1, 1 - l)
  have hcoeff (k : Fin 4) (l : ℤ) :
      act[t ^ l * p ^ (k : ℕ),κ] = ((coeff k l).1 : ℤ) • κ + (coeff k l).2 • δ := by
    rw [normalFormPicard_apply]
    unfold coeff
    split_ifs <;> simp
  have hc := (existsUnique_rotation_apply_boundaryOrthogonalBasis_zero
    (t ^ m * p ^ (i : ℕ))).unique (hcoeff i m)
    ((congrArg (fun g : G ↦ act[g,κ]) h).trans (hcoeff j n))
  have hmn : m = n := by
    dsimp only [coeff] at hc
    split_ifs at hc <;> simp_all
  subst n
  -- With the same translation on both sides, the boundary image distinguishes the powers.
  have hp := congrArg (fun g : G ↦ act[g,D 0]) (mul_left_cancel h)
  simp only [quarterTurn_pow_apply_boundary_zero] at hp
  have hinj : Function.Injective (fun k : Fin 4 ↦ D (-(2 : ZMod 8) * (k : ℕ))) := by decide
  exact Prod.ext (hinj hp) rfl

private theorem reflection_sign_pow (e : Fin 2) :
    sign H D (boundaryReflection ^ (e : ℕ)) = (-1 : ℤˣ) ^ (e : ℕ) := by
  rw [map_pow, sign_apply, boundaryReflection_sign]

private theorem signedNormalFormPicard_bijective :
    Function.Bijective (fun a : Fin 2 × Fin 4 × ℤ ↦
      boundaryReflection ^ (a.1 : ℕ) * incl (t ^ a.2.2 * p ^ (a.2.1 : ℕ))) := by
  constructor
  · rintro ⟨e, i, m⟩ ⟨f, j, n⟩ h
    have hs := congrArg (sign H D) h
    simp only [map_mul, map_pow, sign_apply, boundaryReflection_sign, coe_rotationInclusion,
      one_pow, mul_one] at hs
    have hinj : Function.Injective (fun e : Fin 2 ↦ (-1 : ℤˣ) ^ (e : ℕ)) := by decide
    obtain rfl := hinj hs
    exact Prod.ext rfl (normalFormPicard_injective (rotationInclusion_injective H D
      (mul_left_cancel h)))
  · intro g
    obtain ⟨e, he⟩ : ∃ e : Fin 2, (-1 : ℤˣ) ^ (e : ℕ) = sign H D g := by
      rcases Int.units_eq_one_or (sign H D g) with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    let u := boundaryReflection ^ (e : ℕ)
    have hk : u⁻¹ * g ∈ (sign H D).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, reflection_sign_pow, he, inv_mul_cancel]
    rw [← range_rotationInclusion] at hk
    obtain ⟨r, hr⟩ := hk
    obtain ⟨⟨i, m⟩, rfl⟩ := normalFormPicard_surjective r
    exact ⟨⟨e, i, m⟩, (eq_mul_of_inv_mul_eq hr.symm).symm⟩

private theorem exists_picardEquiv_with_generators :
    ∃ ρ : Γ̂ᵐᵒᵖ ≃* Ĝ,
      ((sign H D).comp ρ.toMonoidHom).ker.unop =
        (clusterModularGroupInclusion ℂ B).range ∧
      ρ (op eval[rotationWord]) = incl p ∧
      ρ (op eval[translationWord]) = incl t ∧
      ρ (op eval[reflectionWord]) = boundaryReflection := by
  obtain ⟨ρ, hk, hw⟩ := exists_four_vertex_marked_picard_equiv
  have hcompare (w : Word B B) :=
    (picardInvariants_eq_signedLoopInvariants_iff _ w).mpr
      ⟨(hw w).1, (hw w).2.1, by
        obtain ⟨j, hj, hj'⟩ := (hw w).2.2
        exact ⟨j, hj', hj.symm⟩⟩
  exact ⟨ρ, hk, (picardInvariants_eq_rotationWord_iff _).mp (hcompare _),
    (picardInvariants_eq_translationWord_iff _).mp (hcompare _),
    (picardInvariants_eq_reflectionWord_iff _).mp (hcompare _)⟩

/-- Every unsigned four-vertex X map has a unique expression `π₂ ^ i * T ^ m`,
where `0 ≤ i < 4` and `m` is any integer. Multiplication is point-map composition. -/
theorem existsUnique_unsigned_normal_form (g : Γ) :
    ∃! a : Fin 4 × ℤ,
      unsigned[rotationWord,inversionCount_rotationWord] ^ (a.1 : ℕ) *
        unsigned[translationWord,inversionCount_translationWord] ^ a.2 = g := by
  obtain ⟨ρ, hk, hp, ht, -⟩ := exists_picardEquiv_with_generators
  let f := ρ.toMonoidHom.comp (clusterModularGroupInclusion ℂ B).op
  have hfinj : Function.Injective f := ρ.injective.comp
    (op_injective.comp ((clusterModularGroupInclusion_injective ℂ B).comp unop_injective))
  have hmem : f (op g) ∈ (sign H D).ker := by
    have hg : clusterModularGroupInclusion ℂ B g ∈
        ((sign H D).comp ρ.toMonoidHom).ker.unop := by
      rw [hk]
      exact ⟨g, rfl⟩
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (Subgroup.mem_unop.mp hg))
  rw [← range_rotationInclusion] at hmem
  obtain ⟨r, hr⟩ := hmem
  have heval (a : Fin 4 × ℤ) :
      f (op (unsigned[rotationWord,inversionCount_rotationWord] ^ (a.1 : ℕ) *
        unsigned[translationWord,inversionCount_translationWord] ^ a.2)) =
      incl (t ^ a.2 * p ^ (a.1 : ℕ)) := by
    simp only [f, op_mul, op_pow, op_zpow, map_mul, map_pow, map_zpow, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MonoidHom.op_apply_apply, Function.comp_apply, unop_op,
      clusterModularGroupInclusion_clusterModularGroupMap, hp, ht]
  obtain ⟨a, ha⟩ := normalFormPicard_surjective r
  refine ⟨a, op_injective (hfinj ((heval a).trans ((congrArg incl ha).trans hr))), ?_⟩
  intro b hb
  apply normalFormPicard_injective
  apply rotationInclusion_injective H D
  exact (heval b).symm.trans ((congrArg (fun x ↦ f (op x)) hb).trans
    (hr.symm.trans (congrArg incl ha).symm))

/-- Every signed four-vertex X map has a unique expression `π₂ ^ i * T ^ m * π₁ ^ e`,
where `0 ≤ i < 4`, `m` is any integer and `e` is zero or one. The last exponent records
the sign. Multiplication is point-map composition. -/
theorem existsUnique_signed_normal_form (g : Γ̂) :
    ∃! a : Fin 2 × Fin 4 × ℤ,
      eval[rotationWord] ^ (a.2.1 : ℕ) * eval[translationWord] ^ a.2.2 *
        eval[reflectionWord] ^ (a.1 : ℕ) = g := by
  obtain ⟨ρ, -, hp, ht, hs⟩ := exists_picardEquiv_with_generators
  have heval (a : Fin 2 × Fin 4 × ℤ) :
      ρ (op (eval[rotationWord] ^ (a.2.1 : ℕ) * eval[translationWord] ^ a.2.2 *
        eval[reflectionWord] ^ (a.1 : ℕ))) =
      boundaryReflection ^ (a.1 : ℕ) * incl (t ^ a.2.2 * p ^ (a.2.1 : ℕ)) := by
    simp only [op_mul, op_pow, op_zpow, map_mul, map_pow, map_zpow, hp, ht, hs]
  obtain ⟨a, ha⟩ := signedNormalFormPicard_bijective.surjective (ρ (op g))
  refine ⟨a, op_injective (ρ.injective ((heval a).trans ha)), ?_⟩
  intro b hb
  exact signedNormalFormPicard_bijective.injective ((heval b).symm.trans
    ((congrArg (fun x ↦ ρ (op x)) hb).trans ha.symm))

end QPainleve.FourVertex
