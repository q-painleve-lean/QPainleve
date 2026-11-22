/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Factorization

import TauCeti.Algebra.BigOperators.ZPow

/-!
# Charge kernels under cluster mutation

An integer charge map from the exponent lattice pulls an alternating form back to the
exchange matrix. Mutating the charges changes this form by congruence and induces an
integral equivalence of the charge kernels. The binomial factor in cluster X mutation
cancels on the kernel, so the same equivalence transports monomial exponents.

The basis change and the X coordinate formulas follow Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.2 and §1.2.4.
The change of basis uses Tau Ceti's `matrixMutationRight` at sign `-1`.
-/

public section

namespace QPainleve.Cluster

open LinearMap (BilinForm)
open Matrix TauCeti
open scoped BigOperators Int

variable {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N]

/-- The exchange matrix of a charge map, in the standard basis of the exponent lattice. -/
def chargeExchangeMatrix (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) : Matrix ι ι ℤ :=
  (BilinForm.comp ω v v).toMatrix'

/-- The entries are the pairings of the corresponding charges. -/
@[simp]
theorem chargeExchangeMatrix_apply (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (i j : ι) :
    chargeExchangeMatrix ω v i j = ω (v (Pi.single i 1)) (v (Pi.single j 1)) := by
  simp [chargeExchangeMatrix, BilinForm.comp_apply]

/-- An alternating charge form gives the unit skew-symmetrizer. -/
theorem isSkewSymmetrizer_chargeExchangeMatrix (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (v : (ι → ℤ) →ₗ[ℤ] N) : (chargeExchangeMatrix ω v).IsSkewSymmetrizer (fun _ ↦ 1) where
  pos _ := Int.one_pos
  mul_apply i j := by simp [hω.neg_eq]

/-- Each row pairs a basis charge with the total charge of an exponent vector. -/
theorem chargeExchangeMatrix_mulVec (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N)
    (x : ι → ℤ) (i : ι) :
    (chargeExchangeMatrix ω v *ᵥ x) i = ω (v (Pi.single i 1)) (v x) := by
  have h := Matrix.toBilin'_apply' (chargeExchangeMatrix ω v) (Pi.single i 1) x
  simpa [chargeExchangeMatrix, BilinForm.comp_apply, single_dotProduct] using h.symm

/-- Every charge relation is an exchange-matrix relation, at any rank. -/
theorem ker_le_ker_chargeExchangeMatrix (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) :
    v.ker ≤ (chargeExchangeMatrix ω v).mulVecLin.ker := by
  intro x hx
  ext i
  simp [chargeExchangeMatrix_mulVec, LinearMap.mem_ker.mp hx]

/-- If the charges span the lattice rationally, the exchange matrix has exactly the charge
kernel. The rank hypothesis allows the image of the charge map to have finite index. -/
theorem ker_chargeExchangeMatrix (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N)
    [Module.Free ℤ N] [Module.Finite ℤ N] (hω : ω.SeparatingRight)
    (hrank : Module.finrank ℤ v.range = Module.finrank ℤ N) :
    (chargeExchangeMatrix ω v).mulVecLin.ker = v.ker := by
  apply le_antisymm _ (ker_le_ker_chargeExchangeMatrix ω v)
  intro x hx
  rw [LinearMap.mem_ker]
  let : Finite (N ⧸ v.range) := Submodule.finiteQuotientOfFreeOfRankEq v.range hrank
  apply hω (v x)
  intro y
  have hzero (z : ι → ℤ) : ω (v z) (v x) = 0 := by
    have h := Matrix.toBilin'_apply' (chargeExchangeMatrix ω v) z x
    have hx' : chargeExchangeMatrix ω v *ᵥ x = 0 := LinearMap.mem_ker.mp hx
    rw [hx', dotProduct_zero] at h
    simpa only [chargeExchangeMatrix, Matrix.toBilin'_toMatrix', BilinForm.comp_apply] using h
  obtain ⟨n, hn, hn'⟩ := (isOfFinAddOrder_of_finite (v.range.mkQ y)).exists_nsmul_eq_zero
  have hmem : n • y ∈ v.range := by
    rwa [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hn'
  obtain ⟨z, hz⟩ := hmem
  have hy : n • ω y (v x) = 0 := by
    calc
      n • ω y (v x) = ω (n • y) (v x) := (map_nsmul (ω.flip (v x)) n y).symm
      _ = 0 := hz ▸ hzero z
  rw [nsmul_eq_mul] at hy
  exact (mul_eq_zero.mp hy).resolve_left (Int.natCast_ne_zero.mpr hn.ne')

/-- The integral change from mutated exponents to original exponents. Its matrix is the
negative-sign right factor of exchange matrix mutation. -/
def chargeMutationEquiv (B : Matrix ι ι ℤ) (k : ι) : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
  LinearEquiv.ofInvolutive (matrixMutationRight (Function.Embedding.refl ι) B k (-1)).mulVecLin
    fun x ↦ by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, matrixMutationRight_mul_self,
        Matrix.one_mulVec]

/-- The basis change acts by multiplication by the right mutation factor. -/
theorem chargeMutationEquiv_apply (B : Matrix ι ι ℤ) (k : ι) (x : ι → ℤ) :
    chargeMutationEquiv B k x = matrixMutationRight (Function.Embedding.refl ι) B k (-1) *ᵥ x :=
  (rfl)

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
    simp [chargeMutationEquiv_apply]
  · simp [chargeMutationEquiv_apply_of_ne _ hi, hi]

/-- Away from the pivot the basis change adds the positive part of the negated pivot row
coefficient times the pivot generator. -/
theorem chargeMutationEquiv_single_of_ne (E : Matrix ι ι ℤ) (p : ι) {i : ι} (hi : i ≠ p) :
    chargeMutationEquiv E p (Pi.single i 1) = Pi.single i 1 + (-E p i)⁺ • Pi.single p 1 := by
  ext j
  by_cases hj : j = p
  · subst j
    simp [chargeMutationEquiv_apply, matrixMutationRight_apply_row, hi, Ne.symm hi]
  · simp [chargeMutationEquiv_apply_of_ne _ hj, hj]

/-- Mutation of the charge map by precomposition with the integral basis change. -/
def chargeMutation (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) :
    (ι → ℤ) →ₗ[ℤ] N :=
  v.comp (chargeMutationEquiv (chargeExchangeMatrix ω v) k).toLinearMap

/-- Evaluate the original charge map on the transported exponent. -/
theorem chargeMutation_apply (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) (x : ι → ℤ) :
    chargeMutation ω v k x = v (chargeMutationEquiv (chargeExchangeMatrix ω v) k x) :=
  (rfl)

/-- Charge mutation preserves the image in the ambient lattice, including its index. -/
@[simp]
theorem range_chargeMutation (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) :
    (chargeMutation ω v k).range = v.range :=
  (chargeMutationEquiv (chargeExchangeMatrix ω v) k).range_comp v

/-- At the pivot, charge mutation negates the corresponding charge. -/
@[simp]
theorem chargeMutation_single_self (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) :
    chargeMutation ω v k (Pi.single k 1) = -v (Pi.single k 1) := by
  simp only [chargeMutation_apply, chargeMutationEquiv_single_self, map_neg]

/-- Away from the pivot, mutation adds the positive part of the exchange coefficient times
the pivot charge. -/
@[simp]
theorem chargeMutation_single_of_ne (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (v : (ι → ℤ) →ₗ[ℤ] N) {k i : ι} (hi : i ≠ k) :
    chargeMutation ω v k (Pi.single i 1) =
      v (Pi.single i 1) + (chargeExchangeMatrix ω v i k)⁺ • v (Pi.single k 1) := by
  rw [chargeMutation_apply, chargeMutationEquiv_single_of_ne _ _ hi, map_add, LinearMap.map_smul]
  simp only [chargeExchangeMatrix_apply, hω.neg_eq]

/-- Computing the exchange matrix from mutated charges agrees with matrix mutation. -/
theorem chargeExchangeMatrix_chargeMutation (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) :
    chargeExchangeMatrix ω (chargeMutation ω v k) =
      matrixMutation (Function.Embedding.refl ι) (chargeExchangeMatrix ω v) k := by
  let B := chargeExchangeMatrix ω v
  let row := Function.Embedding.refl ι
  let F := matrixMutationRight row B k (-1)
  have hF : Fᵀ = matrixMutationLeft row B k (-1) := by
    ext i j
    simp [F, row, B, matrixMutationRight_apply, matrixMutationLeft_apply, hω.neg_eq,
      Matrix.one_apply, eq_comm]
  have hkk : B k k = 0 := by simp [B, hω.self_eq_zero]
  calc
    chargeExchangeMatrix ω (chargeMutation ω v k) = Fᵀ * B * F := by
      have he : (chargeMutationEquiv B k).toLinearMap = F.toLin' :=
        LinearMap.ext fun _ ↦ chargeMutationEquiv_apply _ _ _
      rw [chargeExchangeMatrix, chargeMutation, he]
      rw [← BilinForm.comp_comp, BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin']
      rfl
    _ = matrixMutation row B k := by
      rw [hF, matrixMutation_eq_mul row B k (-1) hkk (Or.inr rfl)]

/-- Mutation restricts to an equivalence from the new charge kernel to the old one. -/
def chargeKernelMutation (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) :
    (chargeMutation ω v k).ker ≃ₗ[ℤ] v.ker :=
  (LinearEquiv.ofEq _ _ (LinearMap.ker_comp _ _)).trans
    ((chargeMutationEquiv (chargeExchangeMatrix ω v) k).ofSubmodule' v.ker)

/-- Kernel transport has the same exponent action as the ambient basis change. -/
@[simp]
theorem coe_chargeKernelMutation_apply (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N)
    (k : ι) (x : (chargeMutation ω v k).ker) :
    (chargeKernelMutation ω v k x : ι → ℤ) =
      chargeMutationEquiv (chargeExchangeMatrix ω v) k (x : ι → ℤ) :=
  (rfl)

/-- Inverse kernel transport uses the same involutive basis change on exponents. -/
@[simp]
theorem coe_chargeKernelMutation_symm_apply (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N)
    (k : ι) (x : v.ker) :
    ((chargeKernelMutation ω v k).symm x : ι → ℤ) =
      chargeMutationEquiv (chargeExchangeMatrix ω v) k (x : ι → ℤ) :=
  (rfl)

/-- The binomial exponent vanishes on a mutated charge relation. -/
theorem sum_mul_chargeExchangeMatrix_eq_zero (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) (x : (chargeMutation ω v k).ker) :
    ∑ i ∈ Finset.univ.erase k, chargeExchangeMatrix ω v i k * (x : ι → ℤ) i = 0 := by
  have h := congrFun (LinearMap.mem_ker.mp
    (ker_le_ker_chargeExchangeMatrix ω (chargeMutation ω v k) x.property)) k
  rw [Matrix.mulVecLin_apply, chargeExchangeMatrix_chargeMutation ω hω,
    Matrix.mulVec, dotProduct] at h
  simp only [matrixMutation_refl_apply_row, chargeExchangeMatrix_apply, hω.neg_eq] at h
  rwa [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
    hω.self_eq_zero, zero_mul, add_zero, Pi.zero_apply] at h

/-- A monomial with exponent in the mutated charge kernel pulls back under X mutation to
the monomial with the transported exponent. The only required nonvanishing conditions
on the coordinates are at the pivot and its binomial. -/
theorem prod_zpow_xMutation_eq {F : Type*} [Semifield F] (ω : BilinForm ℤ N) (hω : ω.IsAlt)
    (v : (ι → ℤ) →ₗ[ℤ] N) (k : ι) (x : (chargeMutation ω v k).ker)
    (X : ι → F) (hX : X k ≠ 0) (hbin : 1 + X k ≠ 0) :
    (∏ i, (if i = k then (X k)⁻¹ else
      X i * X k ^ (chargeExchangeMatrix ω v i k)⁺ *
        (1 + X k) ^ (-chargeExchangeMatrix ω v i k)) ^ (x : ι → ℤ) i) =
      ∏ i, X i ^ (chargeKernelMutation ω v k x : ι → ℤ) i := by
  let B := chargeExchangeMatrix ω v
  let a := (x : ι → ℤ)
  have hswap (i : ι) : -B k i = B i k := by
    simpa [B] using hω.neg_eq (v (Pi.single k 1)) (v (Pi.single i 1))
  have hsum : ∑ i ∈ Finset.univ.erase k, (-B i k) * a i = 0 := by
    simp only [neg_mul, Finset.sum_neg_distrib, B, a, sum_mul_chargeExchangeMatrix_eq_zero ω hω,
      neg_zero]
  have hprod :
      (∏ i ∈ Finset.univ.erase k, (if i = k then (X k)⁻¹ else
        X i * X k ^ (B i k)⁺ * (1 + X k) ^ (-B i k)) ^ a i) =
      ∏ i ∈ Finset.univ.erase k,
        X i ^ a i * X k ^ ((B i k)⁺ * a i) * (1 + X k) ^ ((-B i k) * a i) := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    simp only [ite_eq_right (Finset.ne_of_mem_erase hi), mul_zpow, zpow_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), hprod]
  simp only [ite_true, inv_zpow, ← zpow_neg, coe_chargeKernelMutation_apply,
    chargeMutationEquiv_apply_self, hswap, B, a]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ (isUnit_iff_ne_zero.mpr hX),
    Finset.prod_zpow_eq_zpow_sum_of_isUnit _ (isUnit_iff_ne_zero.mpr hbin),
    hsum, zpow_zero, mul_one, zpow_add₀ hX]
  have hrest : (∏ i ∈ Finset.univ.erase k, X i ^ chargeMutationEquiv B k a i) =
      ∏ i ∈ Finset.univ.erase k, X i ^ a i := by
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [chargeMutationEquiv_apply_of_ne _ (Finset.ne_of_mem_erase hi)]
  rw [hrest]
  ac_rfl

end QPainleve.Cluster
