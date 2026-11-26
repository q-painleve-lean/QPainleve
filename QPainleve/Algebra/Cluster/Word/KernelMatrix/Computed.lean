/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.KernelMatrix.Basic
public import QPainleve.LinearAlgebra.Matrix.Kernel.Basic

import QPainleve.Algebra.Cluster.Word.Monomial

/-!
# Computable matrices of exchange-kernel transport

The integral kernel algorithm supplies coordinate equivalences at both ends of a
word. Transporting each basis vector and reading its coordinates computes the
columns used for comparing signed loops. The product law uses
`LinearMap.toMatrix_comp` through `Quiver.Path.exchangeKernelMatrix_comp`.
-/

public section

open QPainleve.Cluster

namespace Quiver.Path

variable {r : ℕ} {B C D : SkewExchangeMatrix (Fin r)}

/-- Columns of the word's exchange-kernel pullback in the computed endpoint bases.
Each column stores the coordinates in the initial basis of one terminal basis vector. -/
def computedExchangeKernelColumns (w : Word B C) :
    Vector (Vector ℤ B.matrix.intKernelBasisVectors.1) C.matrix.intKernelBasisVectors.1 :=
  let initial := B.matrix.intKernelBasisEquiv
  let terminal := C.matrix.intKernelBasisEquiv
  let transport := w.exchangeKernelEquiv
  Vector.ofFn fun j ↦
    let x := terminal.symm (Pi.single j 1)
    -- Store the ambient entries before either linear map reads them.
    let xValues := Vector.ofFn (x : Fin r → ℤ)
    let y := transport ⟨fun i ↦ xValues[i.val], by
      simpa only [xValues, Vector.getElem_ofFn, Fin.eta] using x.property⟩
    let yValues := Vector.ofFn (y : Fin r → ℤ)
    Vector.ofFn (initial ⟨fun i ↦ yValues[i.val], by
      simpa only [yValues, Vector.getElem_ofFn, Fin.eta] using y.property⟩)

/-- The integer matrix of a word's exchange-kernel pullback, in the computed kernel
bases of its initial and terminal exchange matrices. Rows use the initial basis. -/
def computedExchangeKernelMatrix (w : Word B C) :
    Matrix (Fin B.matrix.intKernelBasisVectors.1) (Fin C.matrix.intKernelBasisVectors.1) ℤ :=
  let columns := w.computedExchangeKernelColumns
  Matrix.of fun i j ↦ columns[j.val][i.val]

/-- The matrix entry in row `i` and column `j` is the stored coordinate of that column. -/
theorem computedExchangeKernelMatrix_apply (w : Word B C)
    (i : Fin B.matrix.intKernelBasisVectors.1) (j : Fin C.matrix.intKernelBasisVectors.1) :
    w.computedExchangeKernelMatrix i j = w.computedExchangeKernelColumns[j.val][i.val] :=
  (rfl)

/-- Each column gives the computed basis coordinates of a transported basis vector. -/
theorem computedExchangeKernelColumns_getElem (w : Word B C)
    (i : Fin B.matrix.intKernelBasisVectors.1) (j : Fin C.matrix.intKernelBasisVectors.1) :
    w.computedExchangeKernelColumns[j.val][i.val] =
      B.matrix.intKernelBasisEquiv (w.exchangeKernelEquiv
        (C.matrix.intKernelBasisEquiv.symm (Pi.single j 1))) i := by
  simp only [computedExchangeKernelColumns, Vector.getElem_ofFn, Fin.eta, Subtype.eta]

/-- The computed matrix represents the exchange-kernel pullback in the endpoint bases. -/
theorem computedExchangeKernelMatrix_eq (w : Word B C) :
    w.computedExchangeKernelMatrix =
      w.exchangeKernelMatrix B.matrix.intKernelBasis C.matrix.intKernelBasis := by
  ext i j
  rw [computedExchangeKernelMatrix_apply, computedExchangeKernelColumns_getElem,
    exchangeKernelMatrix_apply,
    Matrix.intKernelBasisEquiv_symm_single, ← Matrix.intKernelBasis_equivFun,
    Module.Basis.equivFun_apply]

/-- Two computed matrices agree exactly when their exchange-kernel pullbacks agree. -/
theorem computedExchangeKernelMatrix_eq_iff (w v : Word B C) :
    w.computedExchangeKernelMatrix = v.computedExchangeKernelMatrix ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  simp only [computedExchangeKernelMatrix_eq, exchangeKernelMatrix_def, EquivLike.apply_eq_iff_eq,
    LinearEquiv.toLinearMap_inj]

/-- Comparing the stored columns is equivalent to comparing the underlying kernel pullbacks. -/
theorem computedExchangeKernelColumns_eq_iff (w v : Word B C) :
    w.computedExchangeKernelColumns = v.computedExchangeKernelColumns ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  rw [← computedExchangeKernelMatrix_eq_iff]
  constructor
  · intro h
    ext i j
    simp only [computedExchangeKernelMatrix_apply, h]
  · intro h
    apply Vector.ext
    intro j hj
    apply Vector.ext
    intro i hi
    simpa only [computedExchangeKernelMatrix_apply] using
      congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩

/-- The empty word computes the identity matrix. -/
@[simp]
theorem computedExchangeKernelMatrix_nil :
    (Path.nil : Word B B).computedExchangeKernelMatrix = 1 := by
  rw [computedExchangeKernelMatrix_eq, exchangeKernelMatrix_nil]

/-- Concatenation multiplies the computed matrices in pullback order. -/
theorem computedExchangeKernelMatrix_comp (w : Word B C) (v : Word C D) :
    (w.comp v).computedExchangeKernelMatrix =
      w.computedExchangeKernelMatrix * v.computedExchangeKernelMatrix := by
  simp only [computedExchangeKernelMatrix_eq]
  exact w.exchangeKernelMatrix_comp v B.matrix.intKernelBasis C.matrix.intKernelBasis
    D.matrix.intKernelBasis

/-- Appending a step multiplies by its computed matrix on the right. -/
theorem computedExchangeKernelMatrix_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).computedExchangeKernelMatrix =
      w.computedExchangeKernelMatrix * s.toPath.computedExchangeKernelMatrix := by
  simp only [computedExchangeKernelMatrix_eq]
  exact w.exchangeKernelMatrix_cons s B.matrix.intKernelBasis C.matrix.intKernelBasis
    D.matrix.intKernelBasis

/-- Multiplying by the matrix of the reverse word recovers the identity. -/
@[simp]
theorem computedExchangeKernelMatrix_mul_reverse (w : Word B C) :
    w.computedExchangeKernelMatrix * w.reverse.computedExchangeKernelMatrix = 1 := by
  rw [← computedExchangeKernelMatrix_comp, ← computedExchangeKernelMatrix_nil (B := B),
    computedExchangeKernelMatrix_eq_iff]
  simp

end Quiver.Path
