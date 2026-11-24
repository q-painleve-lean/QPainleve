/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Algebra.Cluster.Word.Exponent

import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integer data of a signed cluster loop

Given a basis of the exchange kernel and a table of boundary orders, a loop gives
its inversion sign, an integer matrix, and the result of the boundary label search.
The boundary input consists of the orders along component zero and the table of
orders of the surviving rays in boundary order.
-/

public section

open CategoryTheory QPainleve.Cluster

namespace Quiver.Path

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {E : SkewExchangeMatrix ι}

local notation "K" => LinearMap.ker (Matrix.mulVecLin (SkewExchangeMatrix.matrix E))
local notation "trop[" w "]" =>
  DFunLike.coe (F := Equiv.Perm (ι → ℤ))
    (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) ι)) w)

/-- The inversion sign, the matrix of transported basis vectors in ambient
coordinates, and the first target label whose order vector agrees with the
tropical image of the source vector. Given a basis of the exchange kernel as
integer vectors, the matrix determines the action on the entire kernel. -/
def signedLoopInvariants (w : Word E E) (basisVectors : κ → ι → ℤ)
    (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    ℤˣ × Matrix ι κ ℤ × Option (Fin n) :=
  ((-1) ^ w.inversionCount, Matrix.of (fun i j ↦ w.exponentEquiv (basisVectors j) i),
    Fin.find? fun j ↦ decide (orders j = trop[w] source))

/-- The components of the finite comparison, in the order sign, exponent
matrix, and boundary label. -/
theorem signedLoopInvariants_def (w : Word E E) (basisVectors : κ → ι → ℤ)
    (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    w.signedLoopInvariants basisVectors orders source =
      ((-1) ^ w.inversionCount, Matrix.of (fun i j ↦ w.exponentEquiv (basisVectors j) i),
        Fin.find? fun j ↦ decide (orders j = trop[w] source)) :=
  (rfl)

/-- The integer invariants agree exactly when the inversion signs, the square
matrices in the given exchange-kernel basis, and the finite label searches agree.
The computation uses the ambient coordinates of the transported basis vectors. -/
theorem signedLoopInvariants_eq_iff [Fintype κ] [DecidableEq κ]
    (w v : Word E E) (b : Module.Basis κ ℤ K)
    (orders orders' : Fin n → ι → ℤ) (source : ι → ℤ) :
    w.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders source =
      v.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders' source ↔
    ((-1 : ℤˣ) ^ w.inversionCount = (-1 : ℤˣ) ^ v.inversionCount) ∧
      LinearMap.toMatrixAlgEquiv b w.exchangeKernelEquiv.toLinearMap =
        LinearMap.toMatrixAlgEquiv b v.exchangeKernelEquiv.toLinearMap ∧
      (Fin.find? fun j ↦ decide (orders j = trop[w] source)) =
        (Fin.find? fun j ↦ decide (orders' j = trop[v] source)) := by
  have hmatrix : Matrix.of (fun i j ↦ w.exponentEquiv (b j : ι → ℤ) i) =
      Matrix.of (fun i j ↦ v.exponentEquiv (b j : ι → ℤ) i) ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
    constructor
    · intro h
      apply LinearEquiv.toLinearMap_injective
      apply b.ext
      intro j
      apply Subtype.ext
      funext i
      simpa only [LinearEquiv.coe_coe, coe_exchangeKernelEquiv_apply, Matrix.of_apply]
        using congrArg (fun M : Matrix ι κ ℤ ↦ M i j) h
    · intro h
      ext i j
      simpa only [coe_exchangeKernelEquiv_apply, Matrix.of_apply] using
        congrArg (fun e : K ≃ₗ[ℤ] K ↦ (e (b j) : ι → ℤ) i) h
  simp only [signedLoopInvariants_def, Prod.mk.injEq, hmatrix,
    (LinearMap.toMatrixAlgEquiv b).injective.eq_iff, LinearEquiv.toLinearMap_injective.eq_iff]

end Quiver.Path
