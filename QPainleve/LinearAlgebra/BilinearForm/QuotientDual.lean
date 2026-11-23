/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Duals of quotients of perfectly paired modules

The right orthogonal complement of an arbitrary submodule is identified with
the dual of the quotient. The comparison uses Mathlib's
`Submodule.dualQuotEquivDualAnnihilator`.
-/

public section

namespace LinearMap.BilinForm

open Module

variable {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  (B : LinearMap.BilinForm R L) [LinearMap.IsPerfPair B] (S : Submodule R L)

/-- In a perfect pairing, a vector in the right orthogonal complement of `S` defines a
functional on the quotient by `S` by pairing in the second argument. -/
noncomputable def orthogonalEquivDualQuotient : B.orthogonal S ≃ₗ[R] Dual R (L ⧸ S) :=
  (((LinearMap.flip B).toPerfPair.symm.ofSubmodules S.dualAnnihilator (B.orthogonal S) (by
    rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    exact Submodule.comap_dualAnnihilator_eq_orthogonalBilin B S)).symm).trans
      S.dualQuotEquivDualAnnihilator.symm

/-- The quotient functional evaluates on representatives by the original pairing. -/
@[simp]
theorem orthogonalEquivDualQuotient_apply_mk (x : B.orthogonal S) (y : L) :
    B.orthogonalEquivDualQuotient S x (Submodule.Quotient.mk y) = B y x := by
  simp only [orthogonalEquivDualQuotient, LinearEquiv.trans_apply,
    Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
  -- Expose the ambient functional behind the annihilator subtype's function coercion.
  change (↑_ : Dual R L) y = _
  rw [LinearEquiv.ofSubmodules_symm_apply, LinearEquiv.symm_symm, toPerfPair_apply,
    LinearMap.flip_apply]

end LinearMap.BilinForm
