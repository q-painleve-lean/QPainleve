/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dual.Lemmas

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.GroupTheory.FiniteAbelian.Basic
import TauCeti.Algebra.Module.Submodule.Quotient
import TauCeti.GroupTheory.Torsion
import TauCeti.LinearAlgebra.FreeModule.Int
import TauCeti.LinearAlgebra.Quotient.Prod
import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Cokernels of dual maps of lattices

A section of the map onto the image splits the dual cokernel into the dual of the
kernel and the cokernel of restriction to the image. For a finite free abelian
codomain, the latter factor has order equal to the order of the torsion in the
original cokernel. At full rank this recovers the index of the image.

The splitting uses Mathlib's `Function.Exact.splitSurjectiveEquiv` and
`Module.dualProdDualEquivDual`. The index comparison uses Tau Ceti's
`LinearMap.index_range_eq_natAbs_det_toMatrix`.
-/

public section

open Module

namespace LinearMap

section Split

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

variable (f : M →ₗ[R] N) {s : f.range →ₗ[R] M} (hs : f.rangeRestrict ∘ₗ s = .id)

private noncomputable def kerProdSplitting :
    M ≃ₗ[R] f.ker × f.range := by
  have h : Function.Exact f.ker.subtype f.rangeRestrict :=
    f.ker_rangeRestrict ▸ exact_subtype_ker_map f.rangeRestrict
  exact (h.splitSurjectiveEquiv f.ker.injective_subtype ⟨s, hs⟩).val

private theorem kerProdSplitting_symm_inl (x : f.ker) :
    (f.kerProdSplitting hs).symm (x, 0) = x.val := by
  have h : Function.Exact f.ker.subtype f.rangeRestrict :=
    f.ker_rangeRestrict ▸ exact_subtype_ker_map f.rangeRestrict
  exact (LinearMap.congr_fun (h.splitSurjectiveEquiv f.ker.injective_subtype
    ⟨s, hs⟩).property.1 x).symm

private theorem kerProdSplitting_symm_inr (y : f.range) :
    (f.kerProdSplitting hs).symm (0, y) = s y := by
  have h : Function.Exact f.ker.subtype f.rangeRestrict :=
    f.ker_rangeRestrict ▸ exact_subtype_ker_map f.rangeRestrict
  let e := h.splitSurjectiveEquiv f.ker.injective_subtype
  exact congrArg (fun t : { l : f.range →ₗ[R] M // f.rangeRestrict ∘ₗ l = .id } ↦ t.val y)
    (e.symm_apply_apply ⟨s, hs⟩)

private noncomputable def dualKerProdEquiv : Dual R M ≃ₗ[R] Dual R f.ker × Dual R f.range :=
  (f.kerProdSplitting hs).symm.dualMap.trans (dualProdDualEquivDual R _ _).symm

private theorem dualKerProdEquiv_apply (φ : Dual R M) :
    f.dualKerProdEquiv hs φ = (φ.comp f.ker.subtype, φ.comp s) := by
  ext x <;> simp [dualKerProdEquiv, kerProdSplitting_symm_inl,
    kerProdSplitting_symm_inr]

private theorem map_range_dualMap_dualKerProdEquiv :
    f.dualMap.range.map (f.dualKerProdEquiv hs).toLinearMap =
      (⊥ : Submodule R (Dual R f.ker)).prod f.range.subtype.dualMap.range := by
  rw [← range_comp]
  have h (φ : Dual R N) :
      f.dualKerProdEquiv hs (f.dualMap φ) = (0, f.range.subtype.dualMap φ) := by
    rw [dualKerProdEquiv_apply]
    ext x
    · simp [LinearMap.dualMap_apply, LinearMap.mem_ker.mp x.property]
    · exact congrArg φ (congrArg Subtype.val (LinearMap.congr_fun hs x))
  ext ⟨φ, ψ⟩
  simp [LinearMap.mem_range, h, eq_comm (a := (0 : Dual R f.ker))]

/-- A section onto the image splits the cokernel of the dual map. The factors are
the dual of the kernel and the cokernel of restriction to the image. -/
noncomputable def cokerDualMapEquivProd :
    ((Dual R M) ⧸ f.dualMap.range) ≃ₗ[R]
      Dual R f.ker × ((Dual R f.range) ⧸ f.range.subtype.dualMap.range) :=
  (Submodule.Quotient.equiv _ _ (f.dualKerProdEquiv hs)
    (f.map_range_dualMap_dualKerProdEquiv hs)).trans
    ((Submodule.quotientProdEquiv _ _).trans
      ((Submodule.quotEquivOfEqBot _ rfl).prodCongr (LinearEquiv.refl R _)))

/-- The two coordinates come from restriction to the kernel and pullback along the section. -/
@[simp]
theorem cokerDualMapEquivProd_mk (φ : Dual R M) :
    f.cokerDualMapEquivProd hs (Submodule.Quotient.mk φ) =
      (φ.comp f.ker.subtype, Submodule.Quotient.mk (φ.comp s)) := by
  simp [cokerDualMapEquivProd, dualKerProdEquiv_apply]

end Split

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Between finite free abelian groups of equal rank, a map and its dual have the same
image index. Both indices are zero when the images have infinite index. -/
theorem index_range_dualMap_eq_of_finrank_eq
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (f : M →ₗ[ℤ] N) (hrank : finrank ℤ M = finrank ℤ N) :
    f.dualMap.range.toAddSubgroup.index = f.range.toAddSubgroup.index := by
  let b := Module.finBasis ℤ M
  let c := (Module.finBasis ℤ N).reindex (finCongr hrank.symm)
  rw [f.dualMap.index_range_eq_natAbs_det_toMatrix c.dualBasis b.dualBasis,
    f.index_range_eq_natAbs_det_toMatrix b c, dualMap_def, toMatrix_transpose,
    Matrix.det_transpose]

end LinearMap

namespace Submodule

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/-- The index of the restrictions of integral functionals to a submodule equals the order of
the torsion subgroup of the quotient by that submodule. -/
theorem index_range_subtype_dualMap (P : Submodule ℤ N) :
    P.subtype.dualMap.range.toAddSubgroup.index = Nat.card (AddCommGroup.torsion (N ⧸ P)) := by
  let T := torsion ℤ (N ⧸ P)
  let S := T.comap P.mkQ
  have hle : P ≤ S := le_comap_mkQ P T
  -- The saturation is a direct summand since its quotient is torsion-free.
  let e := P.quotientQuotientEquivQuotient S hle
  have hmap : S.map P.mkQ = T := map_comap_eq_self (by rw [P.range_mkQ]; exact le_top)
  have hfree : Module.IsTorsionFree ℤ (N ⧸ S) :=
    ((quotEquivOfEq _ _ hmap).symm.trans e).symm.injective.moduleIsTorsionFree _
      (map_smul _)
  obtain ⟨Q, hQ⟩ := S.exists_isCompl_iff_isTorsionFree_quotient.mpr hfree
  have hsurj : Function.Surjective S.subtype.dualMap := by
    intro φ
    exact ⟨φ.comp (S.projectionOnto Q hQ), by ext x; simp⟩
  -- On the saturation, the inclusion of P has full rank, and its quotient is T.
  let j := inclusion hle
  let eT : (S ⧸ j.range) ≃ₗ[ℤ] T :=
    (quotEquivOfEq _ _ (by rw [range_inclusion, comap_bot, ker_mkQ])).trans
      ((P.mkQ.comapSubquotientEquivOfSurjective P.mkQ_surjective ⊥ T).trans
        (quotEquivOfEqBot _ (by rw [comap_bot, T.ker_subtype])))
  have : Finite T := Module.finite_of_fg_torsion _ torsion_isTorsion
  have hj : Module.finrank ℤ P = Module.finrank ℤ S := by
    exact (LinearEquiv.ofInjective j (inclusion_injective hle)).finrank_eq.trans
      ((finiteQuotient_iff j.range).mp (Finite.of_injective _ eT.injective))
  have hrange : P.subtype.dualMap.range = j.dualMap.range := by
    rw [← subtype_comp_inclusion P S hle, ← LinearMap.dualMap_comp_dualMap,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]
  rw [hrange, j.index_range_dualMap_eq_of_finrank_eq hj, ← torsion_int]
  exact Nat.card_congr eT.toEquiv

end Submodule

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]

/-- The torsion subgroups of the cokernels of an integral map and its dual have the same order. -/
theorem natCard_torsion_coker_dualMap (f : M →ₗ[ℤ] N) :
    Nat.card (AddCommGroup.torsion ((Dual ℤ M) ⧸ f.dualMap.range)) =
      Nat.card (AddCommGroup.torsion (N ⧸ f.range)) := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  have hindex := f.range.index_range_subtype_dualMap
  have : Finite (Submodule.torsion ℤ (N ⧸ f.range)) :=
    Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion
  have : Finite (AddCommGroup.torsion (N ⧸ f.range)) := by
    rwa [← Submodule.torsion_int]
  have : Finite ((Dual ℤ f.range) ⧸ f.range.subtype.dualMap.range) :=
    AddSubgroup.index_ne_zero_iff_finite.mp (by rw [hindex]; exact Nat.card_pos.ne')
  let : HasUniqueDiv (Dual ℤ f.ker) :=
    Module.isTorsionFree_int_iff_hasUniqueDiv.mp inferInstance
  exact (TauCeti.natCard_torsion_of_mulEquiv isAddTorsion_of_finite
    (f.cokerDualMapEquivProd hs).toAddEquiv.toMultiplicative).trans hindex

/-- If the charge image has full rank, its index is the order of the torsion subgroup
of the cokernel of the dual charge map. -/
theorem natCard_torsion_coker_dualMap_of_finrank_range_eq (f : M →ₗ[ℤ] N)
    (hrank : finrank ℤ f.range = finrank ℤ N) :
    Nat.card (AddCommGroup.torsion ((Dual ℤ M) ⧸ f.dualMap.range)) =
      f.range.toAddSubgroup.index := by
  have : Finite (N ⧸ f.range) := f.range.finiteQuotientOfFreeOfRankEq hrank
  exact f.natCard_torsion_coker_dualMap.trans
    (Nat.card_congr (IsAddTorsion.torsionAddEquiv isAddTorsion_of_finite).toEquiv)

end LinearMap
