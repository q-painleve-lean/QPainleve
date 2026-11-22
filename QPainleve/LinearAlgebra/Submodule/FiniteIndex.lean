/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Isomorphisms

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Prime-index sublattices and extension of isomorphisms

An index-`p` sublattice of a rank-two lattice contains the image of multiplication by
`p` with relative index `p`. Its quotient map to `ZMod p` detects divisibility by `p`
in the ambient lattice. More generally, matching the submodules of ambient multiples
is enough to extend an isomorphism between two sublattices uniquely.
-/

public section

namespace Submodule

variable {M : Type*} [AddCommGroup M]

/-- For a prime-index sublattice of a rank-two free abelian group, the ambient multiples
of the prime are the kernel of a linear functional to the residue field. -/
theorem exists_ker_eq_comap_range_nsmul [Module.Free ℤ M] [Module.Finite ℤ M]
    (H : Submodule ℤ M) (hrank : Module.finrank ℤ M = 2) {p : ℕ} [hp : Fact p.Prime]
    (hindex : H.toAddSubgroup.index = p) :
    ∃ χ : H →ₗ[ℤ] ZMod p,
      χ.ker = ((p • (LinearMap.id : M →ₗ[ℤ] M)).range).comap H.subtype := by
  let P := ((p • (LinearMap.id : M →ₗ[ℤ] M)).range).comap H.subtype
  let S := (nsmulAddMonoidHom (α := M) p).range
  have hle : S ≤ H.toAddSubgroup := by
    rintro _ ⟨x, rfl⟩
    simpa only [nsmulAddMonoidHom_apply, ← hindex] using H.toAddSubgroup.nsmul_index_mem x
  have hS : S.index = p * p := by
    rw [AddSubgroup.index_range_nsmul, hrank, pow_two]
  have hrel : S.relIndex H.toAddSubgroup = p := by
    apply Nat.eq_of_mul_eq_mul_right hp.out.pos
    rw [← hindex, AddSubgroup.relIndex_mul_index hle, hS, hindex]
  -- The relative index is the cardinality of this quotient of the charge image.
  have hcard : Nat.card (H ⧸ P) = p := hrel
  let e : ZMod p ≃+ (H ⧸ P) := hcard ▸
    zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hcard)
  refine ⟨e.symm.toIntLinearEquiv.toLinearMap.comp P.mkQ, ?_⟩
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot_of_injective e.symm.injective,
    Submodule.comap_bot, Submodule.ker_mkQ]

end Submodule

namespace LinearEquiv

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An isomorphism between two sublattices containing the ambient `n`-multiples extends
uniquely to the ambient torsion-free abelian groups if it matches the two submodules
of ambient `n`-multiples. -/
theorem existsUnique_extend_of_nsmul [Module.IsTorsionFree ℤ M]
    [Module.IsTorsionFree ℤ N] {H : Submodule ℤ M} {K : Submodule ℤ N}
    (e : H ≃ₗ[ℤ] K) {n : ℕ} (hn : n ≠ 0)
    (hH : ∀ x : M, n • x ∈ H) (hK : ∀ y : N, n • y ∈ K)
    (he : ∀ x : H, (∃ y : M, n • y = x.val) ↔ ∃ y : N, n • y = (e x).val) :
    ∃! E : M ≃ₗ[ℤ] N, ∀ x : H, E x = (e x).val := by
  let f := (n • (LinearMap.id : M →ₗ[ℤ] M)).codRestrict H hH
  let g := (n • (LinearMap.id : N →ₗ[ℤ] N)).codRestrict K hK
  have hf : Function.Injective f := fun x y h ↦
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn) (congrArg Subtype.val h)
  have hg : Function.Injective g := fun x y h ↦
    (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn) (congrArg Subtype.val h)
  have hf_val (x : M) : (f x).val = n • x := rfl
  have hg_val (y : N) : (g y).val = n • y := rfl
  have hmap : f.range.map e.toLinearMap = g.range := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv]
    simpa only [LinearEquiv.symm_apply_apply, LinearMap.mem_range, Subtype.ext_iff, hf_val, hg_val]
      using he x
  let E := (LinearEquiv.ofInjective f hf).trans
    ((e.ofSubmodules _ _ hmap).trans (LinearEquiv.ofInjective g hg).symm)
  have hE (x : M) : g (E x) = e (f x) := by
    simp [E]
  have hcancel := AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree (M := N) hn
  refine ⟨E, fun x ↦ hcancel ?_, fun E' hE' ↦ ?_⟩
  · have hx : f x = n • x := Subtype.ext rfl
    simpa [g, hx] using congrArg Subtype.val (hE x)
  · ext x
    apply hcancel
    have hx := hE' (f x)
    simpa [f, g, map_nsmul] using hx.trans (congrArg Subtype.val (hE x)).symm

end LinearEquiv
