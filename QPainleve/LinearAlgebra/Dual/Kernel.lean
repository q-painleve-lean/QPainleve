/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.Annihilator

/-!
# The kernel as the dual of a dual cokernel

When the source is reflexive and dual functionals separate points of the target,
the kernel of a map is canonically the dual of the cokernel of its dual map.
The comparison uses the double-dual evaluation equivalence and Tau Ceti's
`LinearMap.kerDualMapEquiv`.
-/

public section

open Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [IsReflexive R M] (f : M →ₗ[R] N)

/-- Vectors in the kernel define functionals on the cokernel of the dual map by evaluation.
This is an equivalence when the source is reflexive and the target embeds in its double dual. -/
noncomputable def kerEquivDualCokerDualMap (hN : Function.Injective (Dual.eval R N)) :
    f.ker ≃ₗ[R] Dual R (Dual R M ⧸ f.dualMap.range) :=
  (((evalEquiv R M).symm.ofSubmodules f.dualMap.dualMap.ker f.ker (by
    rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, ← ker_comp,
      evalEquiv_toLinearMap, Dual.eval_naturality]
    exact ker_comp_of_ker_eq_bot f (ker_eq_bot.mpr hN))).symm).trans f.dualMap.kerDualMapEquiv

/-- The functional associated to a kernel vector evaluates a representative at that vector. -/
@[simp]
theorem kerEquivDualCokerDualMap_apply_mk (hN : Function.Injective (Dual.eval R N))
    (x : f.ker) (φ : Dual R M) :
    f.kerEquivDualCokerDualMap hN x (Submodule.Quotient.mk φ) = φ x := by
  simp [kerEquivDualCokerDualMap]

end LinearMap
