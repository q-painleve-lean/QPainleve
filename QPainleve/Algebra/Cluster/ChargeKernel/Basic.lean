/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import QPainleve.Algebra.Cluster.XMutation.Monomial

import Mathlib.GroupTheory.IndexNSmul
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# Charge kernels under cluster mutation

An integer charge map from the exponent lattice pulls an alternating form back to the
exchange matrix. Equal exchange matrices identify finite-index charge images when the
forms are right-separating. Mutating the charges changes the form by congruence
and induces an integral equivalence of the charge kernels.

The basis change follows Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.2 and §1.2.4.
The charge pairing gives the geometric matrix `ε`. Tau Ceti's exchange convention is
`B = -ε`, so the change of basis uses `matrixMutationRight` on `-ε` at sign `1`.
The charge-image comparison uses Tau Ceti's `LinearMap.equivOfSurjectiveOfKerEq`.
-/

public section

namespace QPainleve.Cluster

open LinearMap (BilinForm)
open Matrix TauCeti
open scoped Int

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

/-- Full-rank charges in a nonzero lattice with a right-separating pairing have a
nonzero exchange matrix. -/
theorem chargeExchangeMatrix_ne_zero_of_finrank_range_eq
    (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N)
    [Module.Free ℤ N] [Module.Finite ℤ N] [Nontrivial N] (hω : ω.SeparatingRight)
    (hrank : Module.finrank ℤ v.range = Module.finrank ℤ N) : chargeExchangeMatrix ω v ≠ 0 := by
  intro hzero
  have hv : v = 0 := by
    rw [← LinearMap.ker_eq_top, ← ker_chargeExchangeMatrix ω v hω hrank, hzero,
      Matrix.mulVecLin_zero, LinearMap.ker_zero]
  rw [hv, LinearMap.range_zero, finrank_bot] at hrank
  exact (Module.finrank_pos (R := ℤ) (M := N)).ne' hrank.symm

/-- Equal exchange matrices identify the images of two finite-index charge maps
for right-separating forms. The equivalence matches charges and preserves their pairings. -/
theorem exists_charge_range_equiv {N₁ N₂ : Type*} [AddCommGroup N₁] [AddCommGroup N₂]
    {ω₁ : BilinForm ℤ N₁} {ω₂ : BilinForm ℤ N₂}
    {v₁ : (ι → ℤ) →ₗ[ℤ] N₁} {v₂ : (ι → ℤ) →ₗ[ℤ] N₂}
    [Module.Free ℤ N₁] [Module.Free ℤ N₂] [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (hω₁ : ω₁.SeparatingRight) (hω₂ : ω₂.SeparatingRight)
    (h₁ : v₁.range.toAddSubgroup.index ≠ 0) (h₂ : v₂.range.toAddSubgroup.index ≠ 0)
    (h : chargeExchangeMatrix ω₁ v₁ = chargeExchangeMatrix ω₂ v₂) :
    ∃ e : v₁.range ≃ₗ[ℤ] v₂.range,
      (∀ x, e (v₁.rangeRestrict x) = v₂.rangeRestrict x) ∧
      ∀ x y : v₁.range, ω₂ (e x).val (e y).val = ω₁ x.val y.val := by
  let : v₁.range.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr h₁
  let : v₂.range.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr h₂
  have hker : v₁.rangeRestrict.ker = v₂.rangeRestrict.ker := by
    rw [LinearMap.ker_rangeRestrict, LinearMap.ker_rangeRestrict]
    calc
      _ = (chargeExchangeMatrix ω₁ v₁).mulVecLin.ker :=
        (ker_chargeExchangeMatrix ω₁ v₁ hω₁
          (AddSubgroup.finrank_eq_of_finiteIndex v₁.range.toAddSubgroup)).symm
      _ = _ := h ▸ ker_chargeExchangeMatrix ω₂ v₂ hω₂
        (AddSubgroup.finrank_eq_of_finiteIndex v₂.range.toAddSubgroup)
  refine ⟨v₁.rangeRestrict.equivOfSurjectiveOfKerEq v₂.rangeRestrict
    v₁.surjective_rangeRestrict v₂.surjective_rangeRestrict hker, by simp, ?_⟩
  have hform : ω₁.comp v₁ v₁ = ω₂.comp v₂ v₂ := BilinForm.toMatrix'.injective h
  intro x y
  obtain ⟨x, rfl⟩ := v₁.surjective_rangeRestrict x
  obtain ⟨y, rfl⟩ := v₁.surjective_rangeRestrict y
  simpa only [LinearMap.equivOfSurjectiveOfKerEq_apply, LinearMap.codRestrict_apply,
    BilinForm.comp_apply] using (congr($hform x y)).symm

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
  let ε := chargeExchangeMatrix ω v
  let row := Function.Embedding.refl ι
  let F := matrixMutationRight row (-ε) k 1
  calc
    chargeExchangeMatrix ω (chargeMutation ω v k) = Fᵀ * ε * F := by
      rw [chargeExchangeMatrix, chargeMutation, ← BilinForm.comp_comp, BilinForm.toMatrix'_comp]
      simp only [chargeMutationEquiv, LinearEquiv.ofInvolutive, LinearMap.toMatrix'_toLin']
      rfl
    _ = matrixMutation row ε k :=
      (ε.matrixMutation_eq_transpose_mul_right (isSkewSymmetrizer_chargeExchangeMatrix ω hω v)
        k).symm

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

end QPainleve.Cluster
