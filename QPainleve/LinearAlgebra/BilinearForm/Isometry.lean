/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.LinearCombination

/-!
# Restrictions of bilinear isometries

An isometry between bilinear forms carries orthogonal complements to orthogonal
complements and restricts to an isometry on corresponding submodules.
For a symmetric nondegenerate form over a field of characteristic different from two,
two isometries agreeing on the orthogonal complement of an isotropic vector agree everywhere.
-/

public section

namespace LinearMap.BilinForm.IsometryEquiv

open LinearMap LinearMap.BilinForm Submodule

section Restriction

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}

/-- A bilinear isometry restricts to an isometry on submodules it identifies. -/
def ofSubmodules (e : B.IsometryEquiv C) (P : Submodule R M) (Q : Submodule R N)
    (h : P.map e.toLinearMap = Q) : (B.restrict P).IsometryEquiv (C.restrict Q) where
  __ := e.toLinearEquiv.ofSubmodules P Q h
  map_app' x y := e.map_app y x

@[simp]
theorem coe_ofSubmodules_apply (e : B.IsometryEquiv C) {P : Submodule R M} {Q : Submodule R N}
    (h : P.map e.toLinearMap = Q) (x : P) : (e.ofSubmodules P Q h x : N) = e x :=
  LinearEquiv.ofSubmodules_apply e.toLinearEquiv h x

@[simp]
theorem coe_ofSubmodules_symm_apply (e : B.IsometryEquiv C) {P : Submodule R M}
    {Q : Submodule R N} (h : P.map e.toLinearMap = Q) (x : Q) :
    ((e.ofSubmodules P Q h).symm x : M) = e.symm x :=
  LinearEquiv.ofSubmodules_symm_apply e.toLinearEquiv h x

/-- The inverse of a composite acts by the inverses in reverse order. -/
@[simp]
theorem symm_trans_apply {L : Type*} [AddCommMonoid L] [Module R L]
    {D : LinearMap.BilinForm R L} (e : B.IsometryEquiv C) (f : C.IsometryEquiv D) (x : L) :
    (e.trans f).symm x = e.symm (f.symm x) := (rfl)

/-- An isometry carries the right orthogonal complement onto the right orthogonal
complement of the image. -/
theorem map_orthogonal (e : B.IsometryEquiv C) (P : Submodule R M) :
    (B.orthogonal P).map e.toLinearMap = C.orthogonal (P.map e.toLinearMap) := by
  ext y
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_orthogonal_iff, mem_orthogonal_iff]
  constructor
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    simpa only [LinearEquiv.coe_coe, coe_toLinearEquiv, e.map_app] using hx z hz
  · intro hx y hy
    simpa only [LinearEquiv.coe_coe, coe_toLinearEquiv, e.map_app] using
      hx _ (Submodule.mem_map_of_mem hy)

end Restriction

variable {K V : Type*} [Field K] [NeZero (2 : K)] [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {g h : B.IsometryEquiv B} {δ : V}

/-- An isometry is determined by its restriction to the orthogonal complement of an isotropic
vector in a symmetric nondegenerate bilinear space over a field of characteristic different
from two. -/
theorem ext_of_eqOn_orthogonal_span_singleton (hB : B.IsSymm) (hsep : B.SeparatingLeft)
    (hδ : B δ δ = 0) (heq : Set.EqOn g h (B.orthogonal (K ∙ δ))) :
    g = h := by
  have hker : B.orthogonal (K ∙ δ) = LinearMap.ker (B δ) := by
    simpa only [BilinForm.orthogonal] using Submodule.orthogonalBilin_span_singleton (B := B) δ
  refine DFunLike.ext _ _ fun x ↦ ?_
  by_cases hx : B δ x = 0
  · exact heq (hker.symm ▸ LinearMap.mem_ker.mpr hx)
  let y := (h : V ≃ₗ[K] V).symm (g x)
  have hy : h y = g x := (h : V ≃ₗ[K] V).apply_symm_apply (g x)
  -- The pairing with the difference vanishes on the kernel of the pairing with δ.
  have hspan : B (y - x) ∈ span K (Set.range fun _ : Unit ↦ B δ) := by
    apply mem_span_of_iInf_ker_le_ker
    intro w hw
    have hwδ : w ∈ B.orthogonal (K ∙ δ) :=
      hker.symm ▸ (Submodule.mem_iInf _).mp hw ()
    rw [mem_ker, sub_left, ← h.map_app w y, hy, ← heq hwδ, g.map_app, sub_self]
  rw [Set.range_const] at hspan
  obtain ⟨a, ha⟩ := mem_span_singleton.mp hspan
  have hdiff : y - x = a • δ := by
    apply (ker_eq_bot.mp (separatingLeft_iff_ker_eq_bot.mp hsep))
    simpa only [map_smul] using ha.symm
  have hnorm : B y y = B x x := by rw [← h.map_app y y, hy, g.map_app]
  rw [sub_eq_iff_eq_add, add_comm] at hdiff
  rw [hdiff] at hnorm
  simp only [add_left, add_right, smul_left, smul_right, hB.eq x δ, hδ, mul_zero, add_zero] at hnorm
  have ha₀ : a = 0 := by
    have hprod : 2 * (a * B δ x) = 0 := by linear_combination hnorm
    have hpair := (mul_eq_zero.mp hprod).resolve_left (NeZero.ne 2)
    exact (mul_eq_zero.mp hpair).resolve_right hx
  simpa [hdiff, ha₀] using hy.symm

end LinearMap.BilinForm.IsometryEquiv
