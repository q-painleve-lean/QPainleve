/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The determinant pairing in rank two

The determinant in an ordered basis of size two gives a perfect alternating pairing and hence
identifies the module with its dual. The construction uses Tau Ceti's `MultilinearMap.toBilinMap`
and `Module.Basis.isPerfPair_of_isUnit_det`.
-/

public noncomputable section

namespace Module.Basis

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-- The determinant in an ordered basis of size two identifies the module with its dual
by sending `h` to the linear functional `u ↦ b.det ![h, u]`. -/
def detDualEquiv (b : Basis (Fin 2) R N) : N ≃ₗ[R] Module.Dual R N := by
  let form := b.det.toMultilinearMap.toBilinMap
  have hmatrix : LinearMap.toMatrix₂ b b form = !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [form, LinearMap.toMatrix₂_apply, Basis.det_apply, Basis.toMatrix_apply,
        Matrix.det_fin_two]
  letI : form.IsPerfPair := b.isPerfPair_of_isUnit_det b form (by
    simp [hmatrix, Matrix.det_fin_two_of])
  exact form.toPerfPair

@[simp]
theorem detDualEquiv_apply (b : Basis (Fin 2) R N) (h u : N) :
    b.detDualEquiv h u = b.det ![h, u] := by
  simp only [detDualEquiv, LinearMap.toPerfPair_apply, MultilinearMap.toBilinMap_apply,
    AlternatingMap.coe_multilinearMap]

end Module.Basis
