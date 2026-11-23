/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod

/-!
# Quotient by the paired range of two linear maps

For a surjection `f : M → P` and a map `g : M → Q`, quotienting `P × Q` by
the pairs `(f x, g x)` eliminates the first summand. The remaining relations
are the images under `g` of the kernel of `f`.
-/

public section

namespace LinearMap

variable {R M P Q : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

variable (f : M →ₗ[R] P) (g : M →ₗ[R] Q)

local notation "j" =>
  LinearMap.comp (Submodule.mkQ (LinearMap.range (LinearMap.prod f g))) (LinearMap.inr R P Q)

private theorem ker_mkQ_comp_inr_prod_range :
    (j).ker = (g.comp f.ker.subtype).range := by
  ext y
  simp only [mem_ker, comp_apply, inr_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_range, prod_apply, Submodule.subtype_apply]
  exact ⟨fun ⟨x, hx⟩ ↦ ⟨⟨x, mem_ker.mpr (congrArg Prod.fst hx)⟩, congrArg Prod.snd hx⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, Prod.ext (mem_ker.mp x.property) hx⟩⟩

private theorem surjective_mkQ_comp_inr_prod_range (hf : Function.Surjective f) :
    Function.Surjective j := by
  intro z
  obtain ⟨⟨p, q⟩, rfl⟩ := (f.prod g).range.mkQ_surjective z
  obtain ⟨x, rfl⟩ := hf p
  refine ⟨q - g x, ?_⟩
  have hpair : ((0 : P), q - g x) + (f x, g x) = (f x, q) := by
    simp
  have hz : (f.prod g).range.mkQ (f x, g x) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact mem_range_self (f.prod g) x
  rw [comp_apply, inr_apply, ← hpair, map_add, hz, add_zero]

/-- If `f` is surjective, the second inclusion induces an equivalence between the quotient
of `Q` by `g(ker f)` and the quotient of `P × Q` by the range of `x ↦ (f x, g x)`. -/
noncomputable def quotientRangeProdEquiv (hf : Function.Surjective f) :
    (Q ⧸ (g.comp f.ker.subtype).range) ≃ₗ[R] ((P × Q) ⧸ (f.prod g).range) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQ_comp_inr_prod_range f g).symm).trans
    ((j).quotKerEquivOfSurjective (surjective_mkQ_comp_inr_prod_range f g hf))

@[simp]
theorem quotientRangeProdEquiv_apply_mk (hf : Function.Surjective f) (y : Q) :
    f.quotientRangeProdEquiv g hf (Submodule.Quotient.mk y) = Submodule.Quotient.mk (0, y) := by
  simp [quotientRangeProdEquiv]

end LinearMap
