/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Bilinear forms on finite-index sublattices

Restricting an integral bilinear form to a full-rank sublattice multiplies the
absolute Gram determinant by the square of its index. This combines Mathlib's
determinant formula for change of basis with `AddSubgroup.index_eq_natAbs_det`.
-/

public section

namespace LinearMap.BilinForm

/-- The absolute Gram determinant on a full-rank sublattice is the absolute Gram
determinant of the ambient form times the index squared. -/
theorem natAbs_det_toMatrix_restrict {N ι : Type*} [AddCommGroup N] [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ N) (S : Submodule ℤ N)
    (b : Module.Basis ι ℤ N) (d : Module.Basis ι ℤ S) :
    ((B.restrict S).toMatrix d).det.natAbs =
      (B.toMatrix b).det.natAbs * S.toAddSubgroup.index ^ 2 := by
  have hrestrict : B.restrict S = B.comp S.subtype S.subtype := by
    ext x y
    simp [restrict_apply, comp_apply]
  have hmatrix : LinearMap.toMatrix d b S.subtype = b.toMatrix (fun i ↦ (d i).val) := by
    ext
    simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
  rw [AddSubgroup.index_eq_natAbs_det b S.toAddSubgroup d, Module.Basis.det_apply,
    hrestrict, toMatrix_comp b d, hmatrix]
  simp [Matrix.det_mul, Matrix.det_transpose, Int.natAbs_mul, pow_two, mul_left_comm, mul_assoc]

end LinearMap.BilinForm
