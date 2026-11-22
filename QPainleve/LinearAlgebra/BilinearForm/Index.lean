/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm

import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Bilinear forms on finite-index sublattices

Restricting an integral bilinear form to a full-rank sublattice multiplies the
absolute Gram determinant by the square of its index. This combines Mathlib's
determinant formula for change of basis with `AddSubgroup.index_eq_natAbs_det`.
In particular, isometric sublattices have the same index in ambient lattices
of Gram determinant one.
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

/-- An alternating form with basis pairing one in rank two has Gram determinant one. -/
theorem det_toMatrix_fin_two_of_apply_eq_one {N : Type*} [AddCommGroup N]
    (ω : LinearMap.BilinForm ℤ N) (b : Module.Basis (Fin 2) ℤ N) (hω : ω.IsAlt)
    (hb : ω (b 0) (b 1) = 1) : (ω.toMatrix b).det = 1 := by
  have h₁₀ : ω (b 1) (b 0) = -1 := by rw [← hω.neg_eq, hb]
  simp [Matrix.det_fin_two, toMatrix_apply, hω (b 0), hω (b 1), hb, h₁₀]

/-- Isometric sublattices in ambient lattices of Gram determinant one have equal index
if the first has finite index. -/
theorem index_eq_of_det_toMatrix_eq_one {N₁ N₂ ι : Type*} [AddCommGroup N₁] [AddCommGroup N₂]
    [Fintype ι] [DecidableEq ι] (ω₁ : LinearMap.BilinForm ℤ N₁) {ω₂ : LinearMap.BilinForm ℤ N₂}
    (b₁ : Module.Basis ι ℤ N₁) (b₂ : Module.Basis ι ℤ N₂)
    (h₁ : (ω₁.toMatrix b₁).det = 1) (h₂ : (ω₂.toMatrix b₂).det = 1)
    {H : Submodule ℤ N₁} {K : Submodule ℤ N₂}
    (hf : H.toAddSubgroup.index ≠ 0) (e : H ≃ₗ[ℤ] K)
    (he : ∀ x y : H, ω₂ (e x).val (e y).val = ω₁ x.val y.val) :
    H.toAddSubgroup.index = K.toAddSubgroup.index := by
  let : Module.Finite ℤ N₁ := Module.Finite.of_basis b₁
  let : Module.Free ℤ N₁ := Module.Free.of_basis b₁
  let : H.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr hf
  have hr : Module.finrank ℤ H = Fintype.card ι :=
    (AddSubgroup.finrank_eq_of_finiteIndex H.toAddSubgroup).trans
      (Module.finrank_eq_card_basis b₁)
  let c : Module.Basis ι ℤ H :=
    (Module.finBasis ℤ H).reindex (Fintype.equivOfCardEq ((Fintype.card_fin _).trans hr))
  have hmat : (ω₁.restrict H).toMatrix c = (ω₂.restrict K).toMatrix (c.map e) := by
    ext i j
    simpa [toMatrix_apply, restrict_apply] using (he (c i) (c j)).symm
  have hsq := congrArg (fun M : Matrix ι ι ℤ ↦ M.det.natAbs) hmat
  simp only [ω₁.natAbs_det_toMatrix_restrict H b₁ c,
    ω₂.natAbs_det_toMatrix_restrict K b₂ (c.map e), h₁, h₂, Int.natAbs_one, one_mul] at hsq
  exact (Nat.pow_left_inj (n := 2) (by decide)).mp hsq

end LinearMap.BilinForm
