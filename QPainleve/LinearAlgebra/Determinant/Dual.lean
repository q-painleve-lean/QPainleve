/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Algebra.Module.Primitive
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

/-- The determinant pairing in the standard basis of the coordinate plane. -/
theorem detDualEquiv_pi_basisFun (x y : Fin 2 → R) :
    (Pi.basisFun R (Fin 2)).detDualEquiv x y = x 0 * y 1 - x 1 * y 0 := by
  rw [detDualEquiv_apply, Basis.det_apply]
  simp [Basis.toMatrix_apply, Matrix.det_fin_two, mul_comm]

/-- Applying a ring homomorphism to both vectors transports the standard determinant pairing. -/
theorem _root_.RingHom.map_detDualEquiv_pi_basisFun {S : Type*} [CommRing S]
    (f : R →+* S) (x y : Fin 2 → R) :
    (Pi.basisFun S (Fin 2)).detDualEquiv (f ∘ x) (f ∘ y) =
      f ((Pi.basisFun R (Fin 2)).detDualEquiv x y) := by
  simp only [detDualEquiv_pi_basisFun, Function.comp_apply, map_sub, map_mul]

/-- Transporting the ordered basis and both arguments preserves the determinant pairing. -/
theorem detDualEquiv_map {N' : Type*} [AddCommGroup N'] [Module R N']
    (b : Basis (Fin 2) R N) (e : N ≃ₗ[R] N') (x y : N) :
    (b.map e).detDualEquiv (e x) (e y) = b.detDualEquiv x y := by
  simp only [detDualEquiv_apply, det_map]
  congr 1
  funext j
  fin_cases j <;> simp

/-- The determinant pairing has value one on the ordered basis. -/
theorem detDualEquiv_apply_basis_zero_one (b : Basis (Fin 2) R N) :
    b.detDualEquiv (b 0) (b 1) = 1 := by
  have h : ![b 0, b 1] = (b : Fin 2 → N) := FinVec.etaExpand_eq b
  rw [detDualEquiv_apply, h, b.det_self]

/-- The determinant pairing is alternating. -/
theorem detDualEquiv_self (b : Basis (Fin 2) R N) (v : N) : b.detDualEquiv v v = 0 := by
  rw [detDualEquiv_apply]
  exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

/-- Interchanging the two inputs negates the determinant pairing. -/
theorem detDualEquiv_swap (b : Basis (Fin 2) R N) (v w : N) :
    b.detDualEquiv v w = -b.detDualEquiv w v := by
  have h : ![w, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, w] := by
    ext j
    fin_cases j <;> rfl
  simpa only [h, detDualEquiv_apply] using
    b.det.map_swap ![w, v] (by decide : (0 : Fin 2) ≠ 1)

/-- Swapping the two basis vectors negates the determinant functional. -/
@[simp]
theorem detDualEquiv_reindex_swap (b : Basis (Fin 2) R N) (v : N) :
    (b.reindex (Equiv.swap 0 1)).detDualEquiv v = -b.detDualEquiv v := by
  ext w
  simpa only [LinearMap.neg_apply, detDualEquiv_apply, det_reindex] using
    b.det.map_swap ![v, w] (by decide : (0 : Fin 2) ≠ 1)

end Module.Basis

namespace Module.Basis

variable {N : Type*} [AddCommGroup N]

/-- An integral vector pairing to one with another vector is primitive. -/
theorem isPrimitive_of_detDualEquiv_eq_one (b : Basis (Fin 2) ℤ N) {x y : N}
    (h : b.detDualEquiv x y = 1) : TauCeti.IsPrimitive x :=
  TauCeti.isPrimitive_def.mpr ⟨-b.detDualEquiv y, by
    rw [LinearMap.neg_apply, detDualEquiv_swap, h, neg_neg]⟩

/-- The determinant functional of a primitive vector takes every integral value. -/
theorem surjective_detDualEquiv_of_isPrimitive (b : Basis (Fin 2) ℤ N) {v : N}
    (hv : TauCeti.IsPrimitive v) : Function.Surjective (b.detDualEquiv v) := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  have h : b.detDualEquiv v (b.detDualEquiv.symm f) = -1 := by
    rw [detDualEquiv_swap, b.detDualEquiv.apply_symm_apply, hf]
  intro z
  refine ⟨(-z) • b.detDualEquiv.symm f, ?_⟩
  rw [map_smul, h]
  simp

end Module.Basis
