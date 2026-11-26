/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic

import Mathlib.LinearAlgebra.Determinant
import QPainleve.LinearAlgebra.Matrix.Index
import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# The charge index from the exchange matrix

For a rank-two charge lattice with determinant pairing, the exchange entries are the
maximal minors of the charge matrix. Their greatest common divisor gives the index of
the charge image. The comparison uses Mathlib's `AlternatingMap.eq_smul_basis_det`
and Tau Ceti's interpretation of alternating bilinear maps.
-/

public section

namespace LinearMap

open Module (Basis)
open QPainleve.Cluster (chargeExchangeMatrix chargeExchangeMatrix_apply)

/-- The index of the charge image is the gcd of the absolute exchange entries for a
determinant pairing on a rank-two lattice. For rank-deficient charges, both sides are zero. -/
theorem index_range_eq_gcd_chargeExchangeMatrix {ι N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup N] (v : (ι → ℤ) →ₗ[ℤ] N) (b : Basis (Fin 2) ℤ N)
    {ω : LinearMap.BilinForm ℤ N} (hω : ω.IsAlt) (hb : ω (b 0) (b 1) = 1) :
    v.range.toAddSubgroup.index =
      Finset.univ.gcd fun ij : ι × ι ↦ (chargeExchangeMatrix ω v ij.1 ij.2).natAbs := by
  have hω' : LinearMap.IsAlt ω := hω
  have hform : hω'.toAlternatingMap = b.det := by
    rw [hω'.toAlternatingMap.eq_smul_basis_det b]
    simp [hb]
  rw [v.index_range_eq_natAbs_minorGcd (Pi.basisFun ℤ ι) b, Matrix.natAbs_minorGcd_fin_two]
  refine Finset.gcd_congr rfl fun ij _ ↦ congrArg Int.natAbs ?_
  have h := DFunLike.congr_fun hform ![v (Pi.single ij.1 1), v (Pi.single ij.2 1)]
  simpa [Matrix.pairMinor_eq, Basis.det_apply, Basis.toMatrix_apply, LinearMap.toMatrix_apply,
    Matrix.det_fin_two] using h.symm

/-- The determinant exchange matrix in a rank-two lattice is zero exactly when
the charge image has infinite index. -/
theorem chargeExchangeMatrix_eq_zero_iff_index_range_eq_zero {ι N : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommGroup N]
    (v : (ι → ℤ) →ₗ[ℤ] N) (b : Basis (Fin 2) ℤ N)
    {ω : LinearMap.BilinForm ℤ N} (hω : ω.IsAlt) (hb : ω (b 0) (b 1) = 1) :
    chargeExchangeMatrix ω v = 0 ↔ v.range.toAddSubgroup.index = 0 := by
  rw [v.index_range_eq_gcd_chargeExchangeMatrix b hω hb, Finset.gcd_eq_zero_iff, ← Matrix.ext_iff]
  simp only [Finset.mem_univ, true_implies, Prod.forall, Int.natAbs_eq_zero, Matrix.zero_apply]

end LinearMap
