/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.MaximalMinor
public import TauCeti.LinearAlgebra.Matrix.Minor

import Mathlib.Algebra.Module.Projective
import TauCeti.LinearAlgebra.FreeModule.Int
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# Image indices from maximal minors

The gcd of the maximal minors of an integral matrix gives the index of its image in the
target lattice. The proof uses Tau Ceti's determinant expansion for a rectangular product
and `Matrix.minorGcd_mul_left`, then applies `LinearMap.index_range_eq_natAbs_det_toMatrix`
to the square inclusion of the image.
-/

public section

open Module

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [CommRing R] [NormalizedGCDMonoid R]

/-- A matrix with a right inverse has relatively prime maximal minors. -/
theorem minorGcd_eq_one_of_mul_eq_one {A : Matrix m n R} {B : Matrix n m R} (h : A * B = 1) :
    A.minorGcd = 1 := by
  classical
  have hdvd : A.minorGcd ∣ (1 : R) := by
    rw [← det_one (n := m), ← h, ← det_transpose, transpose_mul,
      det_mul_eq_sum_prod_mul_det_submatrix]
    refine Finset.dvd_sum fun e _ ↦ dvd_mul_of_dvd_right ?_ _
    rw [← transpose_submatrix, det_transpose]
    by_cases he : Function.Injective e
    · exact A.minorGcd_dvd ⟨e, he⟩
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp he
      rw [det_zero_of_column_eq hne (fun k ↦ by simp [hij])]
      exact dvd_zero _
  exact (normalize_minorGcd A).symm.trans (normalize_eq_one.mpr (isUnit_of_dvd_one hdvd))

/-- In two rows, all ordered column pairs compute the maximal-minor gcd.
Repeated columns contribute zero. -/
theorem natAbs_minorGcd_fin_two (A : Matrix (Fin 2) n ℤ) :
    A.minorGcd.natAbs = Finset.univ.gcd fun ij : n × n ↦ (A.pairMinor (0, 1) ij).natAbs := by
  classical
  have hminor (e : Fin 2 → n) : (A.submatrix id e).det = A.pairMinor (0, 1) (e 0, e 1) := by
    simp [Matrix.det_fin_two, Matrix.pairMinor_eq]
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    rintro ⟨i, j⟩ _
    by_cases hij : i = j
    · subst j
      simp
    · let e : Fin 2 ↪ n := ⟨![i, j], Matrix.injective_pair_iff_ne.mpr hij⟩
      simpa [hminor, e] using Int.natAbs_dvd_natAbs.mpr (A.minorGcd_dvd e)
  · apply Int.natCast_dvd.mp
    apply Matrix.dvd_minorGcd_iff.mpr
    intro e
    rw [Int.natCast_dvd, hminor]
    exact Finset.gcd_dvd (Finset.mem_univ (e 0, e 1))

end Matrix

namespace LinearMap

variable {m n M N : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [AddCommGroup M] [AddCommGroup N]

/-- The index of the image of an integral map is the absolute gcd of the maximal minors of
its matrix. Both sides are zero if the image has smaller rank than the target. -/
theorem index_range_eq_natAbs_minorGcd (f : M →ₗ[ℤ] N)
    (a : Basis n ℤ M) (b : Basis m ℤ N) :
    f.range.toAddSubgroup.index = (toMatrix a b f).minorGcd.natAbs := by
  let := Module.Free.of_basis b
  let := Module.Finite.of_basis b
  classical
  by_cases hr : finrank ℤ f.range = finrank ℤ N
  · let c : Basis m ℤ f.range := (Module.finBasis ℤ f.range).reindex
      (Fintype.equivOfCardEq (by simpa using hr.trans (Module.finrank_eq_card_basis b)))
    let : Module.Projective ℤ f.range := Module.Projective.of_free
    obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
      (range_eq_top.mpr f.surjective_rangeRestrict)
    have hright : toMatrix a c f.rangeRestrict * toMatrix c a s = 1 := by
      rw [← toMatrix_comp, hs, toMatrix_id]
    have hfactor : toMatrix a b f =
        toMatrix c b f.range.subtype * toMatrix a c f.rangeRestrict := by
      rw [← toMatrix_comp, subtype_comp_rangeRestrict]
    rw [hfactor, Matrix.minorGcd_mul_left, Matrix.minorGcd_eq_one_of_mul_eq_one hright, mul_one,
      ← Int.abs_eq_normalize, Int.natAbs_abs]
    simpa only [Submodule.range_subtype] using
      index_range_eq_natAbs_det_toMatrix c b f.range.subtype
  · have hindex : f.range.toAddSubgroup.index = 0 := by
      by_contra h
      exact hr (f.range.finiteQuotient_iff.mp (AddSubgroup.index_ne_zero_iff_finite.mp h))
    have hminor : (toMatrix a b f).minorGcd = 0 := Matrix.minorGcd_eq_zero_iff.mpr fun e ↦ by
      let v : m → f.range := f.rangeRestrict ∘ a ∘ e
      have hdep : ¬ LinearIndependent ℤ v := fun h ↦
        hr (le_antisymm (Submodule.finrank_le f.range)
          ((Module.finrank_eq_card_basis b).trans_le h.fintype_card_le_finrank))
      have hdet := (b.det.compLinearMap f.range.subtype).map_linearDependent v hdep
      rw [AlternatingMap.compLinearMap_apply, Basis.det_apply] at hdet
      convert hdet using 2
      ext i j
      simp [v, Matrix.submatrix_apply, LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    simp [hindex, hminor]

end LinearMap
