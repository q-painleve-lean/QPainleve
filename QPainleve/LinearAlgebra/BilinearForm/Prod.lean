/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# Perfectness of a product of bilinear forms

Perfectness descends to both orthogonal factors. The comparison uses Mathlib's
`Module.dualProdDualEquivDual` for the dual of a product.
-/

public section

namespace LinearMap.BilinForm

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A block-diagonal product pairing is perfect exactly when both factors are perfect. -/
@[simp]
theorem isPerfPair_prod_iff {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N} :
    (B.prod C).IsPerfPair ↔ B.IsPerfPair ∧ C.IsPerfPair := by
  have factors (B' : LinearMap.BilinForm R M) (C' : LinearMap.BilinForm R N)
      (h : Function.Bijective (B'.prod C')) :
      Function.Bijective B' ∧ Function.Bijective C' := by
    let e := Module.dualProdDualEquivDual R M N
    have heq : e.symm ∘ (B'.prod C') = Prod.map B' C' := by
      funext x
      apply e.injective
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
      ext y <;> simp [e]
    exact Prod.map_bijective.mp (heq ▸ e.symm.bijective.comp h)
  refine ⟨fun h ↦ ?_, fun ⟨hB, hC⟩ ↦ inferInstance⟩
  obtain ⟨hB, hC⟩ := factors B C h.bijective_left
  obtain ⟨hB', hC'⟩ := factors B.flip C.flip (flip_prod B C ▸ h.bijective_right)
  exact ⟨⟨hB, hB'⟩, ⟨hC, hC'⟩⟩

end LinearMap.BilinForm
