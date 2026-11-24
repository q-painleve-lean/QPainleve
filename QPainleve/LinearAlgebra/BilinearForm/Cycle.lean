/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Independence in a cycle of vectors

The off-diagonal pairings in a numbered cycle control the rank even when the
self-pairings are arbitrary. Pairing with the preceding vectors gives a
unit lower triangular minor of size `n - 2` for a cycle of length `n`.
-/

public section

namespace LinearMap.BilinForm

/-- For vectors with the off-diagonal pairings of a cycle, the vectors at positions
`1` through `n - 2` are linearly independent. A two-vertex cycle counts both adjacencies. -/
theorem linearIndependent_cycle_segment {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (B : LinearMap.BilinForm R M) {n : ℕ} (v : ZMod n → M)
    (h : ∀ i j, i ≠ j → B (v i) (v j) =
      (if j = i + 1 then 1 else 0) + (if i = j + 1 then 1 else 0)) :
    LinearIndependent R (fun j : Fin (n - 2) ↦ v ((j.val + 1 : ℕ) : ZMod n)) := by
  let test : M →ₗ[R] Fin (n - 2) → R := LinearMap.pi fun i ↦ B (v (i.val : ZMod n))
  let A : Matrix (Fin (n - 2)) (Fin (n - 2)) R :=
    Matrix.of fun i j ↦ test (v ((j.val + 1 : ℕ) : ZMod n)) i
  -- In the upper half of the minor, the index differences are computed before wrapping.
  have hentry (i j : Fin (n - 2)) (hij : i ≤ j) :
      A i j = if i = j then 1 else 0 := by
    have hi := i.isLt
    have hj := j.isLt
    have hle : i.val ≤ j.val := hij
    have hcast (a b : ℕ) (ha : a < n) (hb : b < n) : (a : ZMod n) = b ↔ a = b := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    have hab : (i.val : ZMod n) ≠ ((j.val + 1 : ℕ) : ZMod n) :=
      (hcast _ _ (by omega) (by omega)).not.mpr (by omega)
    have hback : (i.val : ZMod n) ≠ ((j.val + 1 : ℕ) : ZMod n) + 1 := by
      rw [← Nat.cast_one (R := ZMod n), ← Nat.cast_add]
      exact (hcast _ _ (by omega) (by omega)).not.mpr (by omega)
    have hnext : ((j.val + 1 : ℕ) : ZMod n) = (i.val : ZMod n) + 1 ↔ i = j := by
      rw [← Nat.cast_one (R := ZMod n), ← Nat.cast_add, hcast _ _ (by omega) (by omega),
        Nat.add_right_cancel_iff, Fin.val_inj, eq_comm]
    simpa only [A, Matrix.of_apply, test, LinearMap.pi_apply, hnext, hback, ite_false,
      add_zero] using h _ _ hab
  have hA : A.IsLowerTriangular := fun i j hij ↦ by
    have hlt : i < j := hij
    simp only [hentry i j hlt.le, ite_eq_right hlt.ne]
  have hdet : A.det = 1 := by
    rw [A.det_of_isLowerTriangular hA]
    simp [hentry]
  exact LinearIndependent.of_comp test
    (Matrix.linearIndependent_cols_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr
      (hdet.symm ▸ isUnit_one)))

end LinearMap.BilinForm
