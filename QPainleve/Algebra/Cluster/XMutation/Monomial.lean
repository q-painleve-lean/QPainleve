/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ExchangeMatrix.Factorization
public import QPainleve.Algebra.Cluster.XMutation.Symmetry
public import QPainleve.Geometry.Toric.CharacterTorus.Basic

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import TauCeti.Algebra.BigOperators.ZPow

/-!
# Character monomials in cluster X coordinates

A character is the product of the coordinate powers given by its exponent vector.
Relabeling and simultaneous inversion act on these characters by permuting and negating
their exponents, respectively. On the kernel of a mutated square exchange matrix, the
binomial factor of X mutation cancels, and the right mutation factor transports the exponents.

The basis change and the X coordinate formulas follow Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.2 and §1.2.4.
-/

public section

namespace QPainleve.Cluster

section

open CharacterTorus

variable (k : Type*) [Field k] {ι κ : Type*}

/-- A character supported on one label is a power of the corresponding X coordinate. -/
@[simp]
theorem monomial_finsupp_single (i : ι) (n : ℤ) :
    monomial k (Multiplicative.ofAdd (Finsupp.single i n)) = xCoordinate k i ^ n := by
  rw [← Finsupp.smul_single_one i n, ofAdd_zsmul, map_zpow, monomial_ofAdd, ← xCoordinate_def]

/-- Relabeling acts on a character by moving each exponent to its old label. -/
@[simp]
theorem xReindex_apply_monomial (e : κ ≃ ι) (x : κ →₀ ℤ) :
    xReindex k e (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (Finsupp.domCongr e x)) := by
  change (xReindex k e).toAlgHom (monomial k (Multiplicative.ofAdd x)) = _
  rw [xReindex, algEquivOfAlgEquiv_domCongr_toAlgHom, functionFieldMap_monomial,
    AddEquiv.coe_toAddMonoidHom]

/-- Simultaneous X inversion negates the exponent of every character. -/
@[simp]
theorem xInversion_apply_monomial (x : ι →₀ ℤ) :
    xInversion k ι (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (-x)) := by
  change (xInversion k ι).toAlgHom (monomial k (Multiplicative.ofAdd x)) = _
  rw [xInversion, algEquivOfAlgEquiv_domCongr_toAlgHom, functionFieldMap_monomial,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.neg_apply]

variable [Fintype ι]

/-- In independent X coordinates, a lattice character is the product of the coordinate
powers specified by its exponent vector. -/
theorem monomial_eq_prod_zpow_xCoordinate (x : ι → ℤ) :
    monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm x)) =
      ∏ i, xCoordinate k i ^ x i := by
  classical
  rw [Finsupp.equivFunOnFinite_symm_eq_sum, ofAdd_sum, map_prod]
  simp only [monomial_finsupp_single]

end

open Matrix TauCeti
open scoped BigOperators Int

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integral change from mutated exponents to original exponents. Its matrix is the
positive-sign right mutation factor of the native exchange matrix `-ε`. -/
@[expose]
def chargeMutationEquiv (ε : Matrix ι ι ℤ) (k : ι) : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
  LinearEquiv.ofInvolutive (matrixMutationRight (Function.Embedding.refl ι) (-ε) k 1).toLin'
    fun x ↦ by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, matrixMutationRight_mul_self,
        Matrix.one_mulVec]

/-- The basis change acts by the native right mutation factor at sign `1`. -/
theorem chargeMutationEquiv_apply (ε : Matrix ι ι ℤ) (k : ι) (x : ι → ℤ) :
    chargeMutationEquiv ε k x = matrixMutationRight (Function.Embedding.refl ι) (-ε) k 1 *ᵥ x :=
  Matrix.toLin'_apply _ _

/-- The pivot exponent is negated and receives the weighted sum of the other exponents. -/
theorem chargeMutationEquiv_apply_self (B : Matrix ι ι ℤ) (k : ι) (x : ι → ℤ) :
    chargeMutationEquiv B k x k = -x k + ∑ i ∈ Finset.univ.erase k, (-B k i)⁺ * x i := by
  rw [chargeMutationEquiv_apply, Matrix.mulVec, dotProduct,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [matrixMutationRight_apply_row, ↓reduceIte, neg_one_mul]
  rw [add_comm]
  refine congrArg (-x k + ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
  simp [Finset.ne_of_mem_erase hi]

/-- The basis change fixes each nonpivot exponent coordinate. -/
@[simp]
theorem chargeMutationEquiv_apply_of_ne (B : Matrix ι ι ℤ) {k i : ι} (hi : i ≠ k) (x : ι → ℤ) :
    chargeMutationEquiv B k x i = x i := by
  rw [chargeMutationEquiv_apply, Matrix.mulVec, dotProduct]
  simp [matrixMutationRight_apply_of_ne _ _ _ _ hi, Matrix.one_apply]

/-- The mutation basis change negates the pivot generator. -/
@[simp]
theorem chargeMutationEquiv_single_self (E : Matrix ι ι ℤ) (p : ι) :
    chargeMutationEquiv E p (Pi.single p 1) = -Pi.single p 1 := by
  ext i
  by_cases hi : i = p
  · subst i
    simp [chargeMutationEquiv_apply, Matrix.col]
  · simp [hi]

/-- Away from the pivot the basis change adds the positive part of the negated pivot row
coefficient times the pivot generator. -/
theorem chargeMutationEquiv_single_of_ne (E : Matrix ι ι ℤ) (p : ι) {i : ι} (hi : i ≠ p) :
    chargeMutationEquiv E p (Pi.single i 1) = Pi.single i 1 + (-E p i)⁺ • Pi.single p 1 := by
  ext j
  by_cases hj : j = p
  · subst j
    simp [chargeMutationEquiv_apply, Matrix.col, hi, Ne.symm hi]
  · simp [hj, Pi.single_apply]

/-- The binomial exponent in an X mutation vanishes on the mutated exchange-matrix kernel. -/
theorem sum_neg_mul_eq_zero_of_mem_ker_mutation (B : ExchangeMatrix (Function.Embedding.refl ι))
    (k : ι) {x : ι → ℤ} (hx : x ∈ (B.mutation k).matrix.mulVecLin.ker) :
    ∑ i ∈ Finset.univ.erase k, -B.matrix k i * x i = 0 := by
  have h := congrFun (LinearMap.mem_ker.mp hx) k
  have hdiag : B.matrix k k = 0 := B.matrix_row_self k
  rw [ExchangeMatrix.mutation_matrix, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h
  simp only [matrixMutation_refl_apply_row] at h
  rwa [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    hdiag, neg_zero, zero_mul, add_zero, Pi.zero_apply] at h

/-- A monomial in the mutated exchange-matrix kernel pulls back under X mutation to the
monomial with the transported exponent. In the native convention the coefficient is
`B.matrix k i`, which equals `ε i k` when `B.matrix = -ε` is skew-symmetric.
Only the pivot coordinate and its binomial need to be nonzero. -/
theorem prod_zpow_xMutation_eq {F : Type*} [CommGroupWithZero F] [Add F]
    (B : ExchangeMatrix (Function.Embedding.refl ι)) (k : ι) {x : ι → ℤ}
    (hx : x ∈ (B.mutation k).matrix.mulVecLin.ker)
    (X : ι → F) (hX : X k ≠ 0) (hbin : 1 + X k ≠ 0) :
    (∏ i, (if i = k then (X k)⁻¹ else
      X i * X k ^ (B.matrix k i)⁺ * (1 + X k) ^ (-B.matrix k i)) ^ x i) =
      ∏ i, X i ^ chargeMutationEquiv (-B.matrix) k x i := by
  have hprod :
      (∏ i ∈ Finset.univ.erase k, (if i = k then (X k)⁻¹ else
        X i * X k ^ (B.matrix k i)⁺ * (1 + X k) ^ (-B.matrix k i)) ^ x i) =
      ∏ i ∈ Finset.univ.erase k,
        X i ^ x i * X k ^ ((B.matrix k i)⁺ * x i) * (1 + X k) ^ (-B.matrix k i * x i) := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    simp only [ite_eq_right (Finset.ne_of_mem_erase hi), mul_zpow, zpow_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), hprod]
  simp only [ite_true, inv_zpow, ← zpow_neg, chargeMutationEquiv_apply_self, Matrix.neg_apply,
    neg_neg]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ (isUnit_iff_ne_zero.mpr hX),
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ (isUnit_iff_ne_zero.mpr hbin),
    sum_neg_mul_eq_zero_of_mem_ker_mutation B k hx, zpow_zero, mul_one, zpow_add₀ hX]
  have hfixed (i : ι) (hi : i ∈ Finset.univ.erase k) :
      X i ^ chargeMutationEquiv (-B.matrix) k x i = X i ^ x i := by
    rw [chargeMutationEquiv_apply_of_ne _ (Finset.ne_of_mem_erase hi)]
  rw [Finset.prod_congr rfl hfixed]
  ac_rfl

end QPainleve.Cluster
