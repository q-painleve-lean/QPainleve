/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Algebra.Cluster.Word.KernelMatrix
public import QPainleve.Algebra.Cluster.Word.Pullback

import QPainleve.Algebra.Cluster.Tropical.Valuation
import QPainleve.Algebra.Cluster.Word.Monomial
import QPainleve.Algebra.Cluster.Word.Parity

/-!
# Integer data of a signed cluster loop

Given a basis of the exchange kernel and a table of boundary orders, a loop gives
its inversion sign, an integer matrix, and the result of the boundary label search.
The boundary input consists of the orders along component zero and the table of
orders of the surviving rays in boundary order.
-/

public section

open CategoryTheory QPainleve.Cluster

namespace QPainleve.Cluster

/-- The integer data used to compare signed loops. The columns use ambient coordinates,
and the boundary label is the result of the forward search in the order table. -/
@[ext]
structure SignedLoopInvariants (ι κ : Type*) (n : ℕ) where
  /-- The sign of the inversion count. -/
  sign : ℤˣ
  /-- The transported exponent vectors, indexed by column. -/
  kernelColumns : Matrix ι κ ℤ
  /-- The first matching label in the target order table, if one exists. -/
  boundaryLabel : Option (Fin n)

/-- For finite row and column index types, equality is decidable by comparing the three fields. -/
instance {ι κ : Type*} {n : ℕ} [Fintype ι] [Fintype κ] :
    DecidableEq (SignedLoopInvariants ι κ n) :=
  fun x y ↦ decidable_of_iff _ (SignedLoopInvariants.ext_iff (x := x) (y := y)).symm

end QPainleve.Cluster

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
    SignedLoopInvariants ι κ n where
  sign := (-1) ^ w.inversionCount
  kernelColumns := Matrix.of (fun i j ↦ w.exponentEquiv (basisVectors j) i)
  boundaryLabel := Fin.find? fun j ↦ decide (orders j = trop[w] source)

/-- The sign records the parity of the number of inversions. -/
@[simp]
theorem signedLoopInvariants_sign (w : Word E E) (vectors : κ → ι → ℤ)
    (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    (w.signedLoopInvariants vectors orders source).sign = (-1) ^ w.inversionCount :=
  (rfl)

/-- The exponent action sends each supplied vector to a column of the integer invariant. -/
@[simp]
theorem signedLoopInvariants_kernelColumns (w : Word E E) (vectors : κ → ι → ℤ)
    (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    (w.signedLoopInvariants vectors orders source).kernelColumns =
      Matrix.of (fun i j ↦ w.exponentEquiv (vectors j) i) :=
  (rfl)

/-- The boundary label is the first row matching the tropical image of the source orders. -/
theorem signedLoopInvariants_boundaryLabel (w : Word E E) (vectors : κ → ι → ℤ)
    (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    (w.signedLoopInvariants vectors orders source).boundaryLabel =
      Fin.find? fun j ↦ decide (orders j = trop[w] source) :=
  (rfl)

/-- For distinct rows, the label search returns precisely the row with the transported
orders. -/
@[simp]
theorem signedLoopInvariants_boundaryLabel_eq_some_iff (w : Word E E)
    (vectors : κ → ι → ℤ) {orders : Fin n → ι → ℤ} (source : ι → ℤ)
    (hinj : Function.Injective orders) (j : Fin n) :
    (w.signedLoopInvariants vectors orders source).boundaryLabel = some j ↔
      orders j = trop[w] source := by
  simp only [signedLoopInvariants_boundaryLabel, ← Option.mem_def, Fin.mem_find?_iff,
    decide_eq_true_eq]
  exact ⟨And.left, fun h ↦ ⟨h, fun k hk h' ↦ hk.ne (hinj (h'.trans h.symm))⟩⟩

/-- The transported ambient columns are obtained by multiplying the matrix of kernel
coordinates by the matrix of the basis inclusion on the left. -/
theorem signedLoopInvariants_matrix [Fintype κ] [DecidableEq κ]
    (w : Word E E) (b : Module.Basis κ ℤ K) (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    (w.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders source).kernelColumns =
      Matrix.of (fun i j ↦ (b j : ι → ℤ) i) * w.exchangeKernelMatrix b b := by
  have hleft : LinearMap.toMatrix b (Pi.basisFun ℤ ι) (K).subtype =
      Matrix.of (fun i j ↦ (b j : ι → ℤ) i) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [← hleft, exchangeKernelMatrix_def, ← LinearMap.toMatrix_comp b b (Pi.basisFun ℤ ι)]
  ext i j
  simp [LinearMap.toMatrix_apply]

/-- A left inverse of the basis inclusion reads the square matrix of the kernel action
from the transported ambient columns. -/
theorem leftInverse_mul_signedLoopInvariants_matrix [Fintype κ] [DecidableEq κ]
    (w : Word E E) (b : Module.Basis κ ℤ K) (orders : Fin n → ι → ℤ) (source : ι → ℤ)
    (read : Matrix κ ι ℤ) (hread : read * Matrix.of (fun i j ↦ (b j : ι → ℤ) i) = 1) :
    read * (w.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders source).kernelColumns =
      w.exchangeKernelMatrix b b := by
  rw [signedLoopInvariants_matrix, ← Matrix.mul_assoc, hread, Matrix.one_mul]

/-- Given an integer coordinate reader for the specified basis, compose transported
ambient columns by matrix multiplication. The reader is any left inverse of the basis
inclusion matrix, so only its values on the exchange kernel enter the computation. -/
theorem signedLoopInvariants_comp_matrix [Fintype κ] [DecidableEq κ]
    (w v : Word E E) (b : Module.Basis κ ℤ K) (orders : Fin n → ι → ℤ) (source : ι → ℤ)
    (read : Matrix κ ι ℤ) (hread : read * Matrix.of (fun i j ↦ (b j : ι → ℤ) i) = 1) :
    let cols (u : Word E E) :=
      (u.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders source).kernelColumns
    cols (w.comp v) = cols w * (read * cols v) := by
  dsimp only
  rw [v.leftInverse_mul_signedLoopInvariants_matrix b orders source read hread,
    (w.comp v).signedLoopInvariants_matrix b orders source, exchangeKernelMatrix_comp w v b b b,
    ← Matrix.mul_assoc, ← w.signedLoopInvariants_matrix b orders source]

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
      (w.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders source).boundaryLabel =
        (v.signedLoopInvariants (fun j ↦ (b j : ι → ℤ)) orders' source).boundaryLabel := by
  have hmatrix :
      Matrix.of (fun i j ↦ w.exponentEquiv (b j : ι → ℤ) i) =
        Matrix.of (fun i j ↦ v.exponentEquiv (b j : ι → ℤ) i) ↔
      w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
    constructor
    · intro h
      apply LinearEquiv.toLinearMap_injective
      refine b.ext fun j ↦ Subtype.ext (funext fun i ↦ ?_)
      simpa only [Matrix.of_apply, ← coe_exchangeKernelEquiv_apply, LinearEquiv.coe_coe]
        using congrFun (congrFun h i) j
    · intro h
      simp only [← coe_exchangeKernelEquiv_apply, h]
  simp only [SignedLoopInvariants.ext_iff, signedLoopInvariants_sign,
    signedLoopInvariants_kernelColumns, hmatrix, (LinearMap.toMatrixAlgEquiv b).injective.eq_iff,
    LinearEquiv.toLinearMap_injective.eq_iff]

/-- Over any field, equal X pullbacks of loops at a nonzero exchange matrix
give equal integer invariants for every supplied family of exchange-kernel vectors
and every boundary order table. -/
theorem signedLoopInvariants_eq_of_xPullback_eq {k : Type*} [Field k]
    (hE : E.matrix ≠ 0) {w v : Word E E} (h : w.xPullback k = v.xPullback k)
    (vectors : κ → K) (orders : Fin n → ι → ℤ) (source : ι → ℤ) :
    w.signedLoopInvariants (fun j => (vectors j : ι → ℤ)) orders source =
      v.signedLoopInvariants (fun j => (vectors j : ι → ℤ)) orders source := by
  have hsign := neg_one_pow_congr (R := ℤˣ) (even_inversionCount_iff_of_xPullback_eq hE h)
  have hkernel := exchangeKernelEquiv_eq_of_xPullback_eq k h
  have htrop := congrFun (tropical_eq_of_xPullback_eq_of_linearOrder (Γ := ℤ) h) source
  simp only [Equiv.toFun_as_coe] at htrop
  simp only [SignedLoopInvariants.ext_iff, signedLoopInvariants_sign,
    signedLoopInvariants_kernelColumns, signedLoopInvariants_boundaryLabel,
    ← coe_exchangeKernelEquiv_apply, hsign, hkernel, htrop, and_self]

section Conjugation

variable {E' : SkewExchangeMatrix ι}
variable {κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- The Casimir matrix of a loop transported along a connecting word is conjugated
by the matrix of the connecting word's exchange-kernel pullback. The two bases can
have different index types. -/
theorem toMatrix_exchangeKernelEquiv_reverse_comp_comp (w : Word E E') (v : Word E E)
    (b : Module.Basis κ ℤ K) (b' : Module.Basis κ' ℤ E'.matrix.mulVecLin.ker) :
    LinearMap.toMatrix b' b' ((w.reverse.comp v).comp w).exchangeKernelEquiv.toLinearMap =
      LinearMap.toMatrix b b' w.exchangeKernelEquiv.symm.toLinearMap *
        LinearMap.toMatrix b b v.exchangeKernelEquiv.toLinearMap *
        LinearMap.toMatrix b' b w.exchangeKernelEquiv.toLinearMap := by
  rw [exchangeKernelEquiv_comp, exchangeKernelEquiv_comp, exchangeKernelEquiv_reverse]
  simp only [LinearEquiv.coe_trans]
  rw [LinearMap.toMatrix_comp b' b b', LinearMap.toMatrix_comp b b b']

end Conjugation

/-- If a connecting word transports one table of boundary orders by `p`, and a
loop permutes the original table by `q`, then the transported loop's boundary
search at any target label `j` returns `p (q (p.symm j))`. -/
theorem signedLoopInvariants_reverse_comp_comp_boundary
    {E' : SkewExchangeMatrix ι} (w : Word E E') (v : Word E E)
    (basisVectors : κ → ι → ℤ) {orders orders' : Fin n → ι → ℤ}
    (hinj : Function.Injective orders') (p q : Equiv.Perm (Fin n))
    (hw : ∀ j, trop[w] (orders j) = orders' (p j))
    (hv : ∀ j, trop[v] (orders j) = orders (q j)) (j : Fin n) :
    (((w.reverse.comp v).comp w).signedLoopInvariants basisVectors orders'
      (orders' j)).boundaryLabel = some (p (q (p.symm j))) := by
  have hreverse : trop[w.reverse] (orders' j) = orders (p.symm j) := by
    rw [tropical_reverse, SingleObj.inv_as_inv]
    exact (Equiv.symm_apply_eq _).mpr (by
      simpa only [Equiv.apply_symm_apply] using (hw (p.symm j)).symm)
  have himage : trop[(w.reverse.comp v).comp w] (orders' j) = orders' (p (q (p.symm j))) := by
    let F := Paths.lift (tropicalPrefunctor (A := ℤ) ι)
    -- Read the morphisms of the one-object category as permutations.
    let action {B C : SkewExchangeMatrix ι} (s : Word B C) : Equiv.Perm (ι → ℤ) :=
      F.map (X := (Paths.of _).obj B) (Y := (Paths.of _).obj C) s
    have hcomp {B C D : SkewExchangeMatrix ι} (s : Word B C) (t : Word C D) :
        action (s.comp t) = action t * action s :=
      F.map_comp (X := (Paths.of _).obj B) (Y := (Paths.of _).obj C) (Z := (Paths.of _).obj D) s t
    calc
      _ = action ((w.reverse.comp v).comp w) (orders' j) := rfl
      _ = action w (action v (action w.reverse (orders' j))) := by
        rw [hcomp, hcomp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      _ = action w (action v (orders (p.symm j))) := congrArg (action w ∘ action v) hreverse
      _ = action w (orders (q (p.symm j))) := congrArg (action w) (hv (p.symm j))
      _ = _ := hw (q (p.symm j))
  exact (signedLoopInvariants_boundaryLabel_eq_some_iff _ _ _ hinj _).mpr himage.symm

end Quiver.Path
