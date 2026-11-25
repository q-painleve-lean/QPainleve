/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Algebra.Cluster.Word.Basic
public import QPainleve.LinearAlgebra.Determinant.Dual

/-!
# Exchange matrices from integer charge coordinates

An ordered rank-two lattice basis lets the signed cluster word machinery take
integer charge vectors directly as input. The determinant of two charge vectors
gives their exchange entry in the cluster X convention.
-/

public section

namespace QPainleve.Cluster.SkewExchangeMatrix

/-- Construct the exchange matrix of a family of charges in an ordered rank-two frame. -/
def ofChargeCoordinates {ι : Type*} (charge : ι → Fin 2 → ℤ) : SkewExchangeMatrix ι :=
  ofMatrix (Matrix.of fun j k ↦ Matrix.det !![charge j 0, charge j 1; charge k 0, charge k 1])
    ⟨fun _ ↦ Int.zero_lt_one, fun j k ↦ by
      simp only [one_mul, Matrix.of_apply, Matrix.det_fin_two_of]
      ring⟩

/-- The exchange entry is the determinant in the supplied coordinates. -/
@[simp]
theorem ofChargeCoordinates_matrix_apply {ι : Type*} (charge : ι → Fin 2 → ℤ) (j k : ι) :
    (ofChargeCoordinates charge).matrix j k =
      charge j 0 * charge k 1 - charge j 1 * charge k 0 := by
  simp only [ofChargeCoordinates, matrix_ofMatrix, Matrix.of_apply, Matrix.det_fin_two_of]

/-- Computing the exchange matrix in a basis agrees with pairing charges in the lattice. -/
theorem ofChargeCoordinates_matrix_eq_chargeExchangeMatrix {ι N : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommGroup N]
    (b : Module.Basis (Fin 2) ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) :
    (ofChargeCoordinates fun j ↦ b.repr (v (Pi.single j 1))).matrix =
      chargeExchangeMatrix b.detDualEquiv.toLinearMap v := by
  ext j k
  simp [chargeExchangeMatrix_apply, Module.Basis.det_apply, Module.Basis.toMatrix_apply,
    Matrix.det_fin_two, mul_comm]

end QPainleve.Cluster.SkewExchangeMatrix
