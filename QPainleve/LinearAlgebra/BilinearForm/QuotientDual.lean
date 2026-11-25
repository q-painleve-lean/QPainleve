/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import QPainleve.LinearAlgebra.Dual.Cokernel
import TauCeti.LinearAlgebra.Dual.Basis

/-!
# Duals of quotients of perfectly paired modules

The right orthogonal complement of an arbitrary submodule is identified with
the dual of the quotient. The comparison uses Mathlib's
`Submodule.dualQuotEquivDualAnnihilator`.

Over the integers, restriction of functionals has finite-index image, so
the submodule and its orthogonal complement have complementary ranks.
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

/-- Over a principal ideal domain, the left orthogonal of the right orthogonal consists
of the vectors whose classes in the quotient are torsion. -/
theorem mem_flip_orthogonal_orthogonal_iff_quotient_mem_torsion
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R L] {x : L} :
    x ∈ B.flip.orthogonal (B.orthogonal S) ↔
      Submodule.Quotient.mk x ∈ Submodule.torsion R (L ⧸ S) := by
  classical
  let T := Submodule.torsion R (L ⧸ S)
  rw [mem_orthogonal_iff]
  constructor
  · intro hx
    by_contra h
    have hq : T.mkQ (Submodule.Quotient.mk x) ≠ 0 :=
      fun he ↦ h ((Submodule.Quotient.mk_eq_zero T).mp he)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hq
    obtain ⟨y, hy⟩ := (B.orthogonalEquivDualQuotient S).surjective (f.comp T.mkQ)
    apply hf
    rw [← LinearMap.comp_apply, ← hy, orthogonalEquivDualQuotient_apply_mk]
    exact hx y y.property
  · intro hx y hy
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).mp hx
    let f := B.orthogonalEquivDualQuotient S ⟨y, hy⟩
    have hz := congrArg f ha
    simp only [f, Submonoid.smul_def, map_smul, map_zero,
      orthogonalEquivDualQuotient_apply_mk, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (nonZeroDivisors.coe_ne_zero a)

variable {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]

/-- In a perfectly paired finite free integer module, a submodule and its right
orthogonal complement have complementary ranks, including for degenerate restrictions. -/
theorem finrank_add_finrank_orthogonal_int (A : LinearMap.BilinForm ℤ M)
    [A.IsPerfPair] (P : Submodule ℤ M) :
    finrank ℤ P + finrank ℤ (A.orthogonal P) = finrank ℤ M := by
  let : Module.IsTorsionFree ℤ M :=
    (LinearMap.IsPerfPair.bijective_left A).injective.moduleIsTorsionFree A (map_smul A)
  let f := P.subtype.dualMap.comp (LinearMap.flip A).toPerfPair.toLinearMap
  have hker : f.ker = A.orthogonal P := by
    ext x
    simp [f, LinearMap.mem_ker, LinearMap.ext_iff, mem_orthogonal_iff, Subtype.forall]
  have hrange : f.range = P.subtype.dualMap.range := by
    simp [f, LinearMap.range_comp]
  have : Finite (Submodule.torsion ℤ (M ⧸ P)) :=
    Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion
  have : Finite (AddCommGroup.torsion (M ⧸ P)) := by
    rwa [← Submodule.torsion_int]
  have hfinite : Finite (Dual ℤ P ⧸ P.subtype.dualMap.range) :=
    AddSubgroup.index_ne_zero_iff_finite.mp
      (by rw [P.index_range_subtype_dualMap]; exact Nat.card_pos.ne')
  have hrank := P.subtype.dualMap.range.finiteQuotient_iff.mp hfinite
  have h := f.finrank_range_add_finrank_ker
  rwa [hker, hrange, hrank, TauCeti.Module.dual_finrank_eq] at h

end LinearMap.BilinForm
