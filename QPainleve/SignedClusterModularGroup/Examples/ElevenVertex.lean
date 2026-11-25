/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import QPainleve.Algebra.Cluster.ChargeKernel.Basic
public import QPainleve.Algebra.Cluster.Word.Exponent
public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.LinearAlgebra.Determinant.Dual

/-!
# The eleven-vertex seed for a one-component boundary

The labels over the three rays of the projective-plane fan have multiplicities
two, three and six. With zero-based indexing, the two odd loops invert all coordinates,
mutate at zero and one, and in the second loop also exchange those two labels.
The second loop acts by negation on the exchange kernel and has order two on the field
of independent X coordinates. The endpoint and exponent computations use Tau Ceti's
zero-entry mutation lemma and its right mutation factor through the cluster word API.
-/

public section

open Matrix Module Quiver
open scoped Int

namespace QPainleve.ElevenVertex

open Cluster

local notation "I" => Fin 11
local notation "N" => Fin 2 → ℤ

/-- The ray index of each of the eleven labels, in the three consecutive blocks. -/
def rayIndex : I → Fin 3 := ![0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- The three consecutive blocks of center labels lie on rays zero, one and two. -/
theorem rayIndex_eq_ite (i : I) :
    rayIndex i = if i.val < 2 then 0 else if i.val < 5 then 1 else 2 := by
  fin_cases i <;> decide

/-- The first ray carries exactly the first two labels. -/
theorem rayIndex_eq_zero_iff (i : I) : rayIndex i = 0 ↔ i = 0 ∨ i = 1 := by
  fin_cases i <;> decide

/-- The second ray carries the next three labels. -/
theorem rayIndex_eq_one_iff (i : I) : rayIndex i = 1 ↔ i = 2 ∨ i = 3 ∨ i = 4 := by
  fin_cases i <;> decide

/-- The primitive charge of a label in the ordered projective-plane fan. -/
def charge (i : I) : N := (![![1, 0], ![0, 1], ![-1, -1]] : Fin 3 → N) (rayIndex i)

/-- The charges in order of ray index are (1, 0), (0, 1) and (-1, -1). -/
theorem charge_apply (i : I) :
    charge i = (![![1, 0], ![0, 1], ![-1, -1]] : Fin 3 → N) (rayIndex i) :=
  (rfl)

/-- All eleven charges are primitive in the rank-two lattice. -/
theorem isPrimitive_charge (i : I) : TauCeti.IsPrimitive (charge i) := by
  rw [charge_apply]
  generalize rayIndex i = j
  apply TauCeti.isPrimitive_def.mpr
  fin_cases j
  · exact ⟨LinearMap.proj 0, by decide⟩
  · exact ⟨LinearMap.proj 1, by decide⟩
  · exact ⟨-LinearMap.proj 0, by decide⟩

/-- The linear map that sends the standard generators to the eleven charges. -/
noncomputable def chargeMap : (I → ℤ) →ₗ[ℤ] N :=
  (Pi.basisFun ℤ I).constr ℤ charge

/-- On a standard exponent generator the linear charge map returns that label's charge. -/
@[simp]
theorem chargeMap_single (i : I) : chargeMap (Pi.single i 1) = charge i := by
  simpa only [chargeMap, Pi.basisFun_apply] using (Pi.basisFun ℤ I).constr_basis ℤ charge i

private def rayPairing : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, -1; -1, 0, 1; 1, -1, 0]

/-- The exchange matrix in the X-coordinate convention. Its entries depend only
on the rays of the two labels. -/
def exchangeMatrix : SkewExchangeMatrix I :=
  SkewExchangeMatrix.ofMatrix (rayPairing.submatrix rayIndex rayIndex) ⟨
    fun _ ↦ Int.one_pos, fun i j ↦ by
      simp only [Matrix.submatrix_apply, one_mul]
      generalize rayIndex i = a, rayIndex j = b
      fin_cases a <;> fin_cases b <;> decide⟩

local notation "B" => exchangeMatrix
local notation "τ" => Equiv.swap (0 : I) 1
local notation "det₂" => (Basis.detDualEquiv (Pi.basisFun ℤ (Fin 2)))

/-- The exchange matrix is the determinant pairing of the specified charges. -/
theorem exchangeMatrix_eq_chargeExchangeMatrix :
    (B).matrix = chargeExchangeMatrix (det₂).toLinearMap chargeMap := by
  ext i j
  simp only [exchangeMatrix, SkewExchangeMatrix.matrix_ofMatrix, Matrix.submatrix_apply,
    chargeExchangeMatrix_apply, chargeMap_single, charge]
  generalize rayIndex i = a, rayIndex j = b
  simp only [LinearEquiv.coe_coe, Basis.detDualEquiv_apply, Basis.det_apply, Basis.toMatrix_apply,
    Pi.basisFun_repr, Matrix.det_fin_two]
  fin_cases a <;> fin_cases b <;> decide

private theorem reindex_swap : (B).reindex τ = B := by
  apply SkewExchangeMatrix.ext
  have h : rayIndex ∘ τ = rayIndex := by
    funext i
    fin_cases i <;> decide
  simp only [SkewExchangeMatrix.reindex_matrix, Equiv.symm_swap, exchangeMatrix,
    SkewExchangeMatrix.matrix_ofMatrix, Matrix.submatrix_submatrix, h]

private theorem mutate_inverted_twice : ((-B).mutate 0).mutate 1 = B := by
  apply SkewExchangeMatrix.ext
  ext i j
  simp only [SkewExchangeMatrix.mutate_matrix, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply,
    exchangeMatrix, SkewExchangeMatrix.matrix_ofMatrix, TauCeti.matrixMutation_apply,
    Function.Embedding.refl_apply, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;> decide

private theorem inverted_mutate_zero_col_one (i : I) :
    ((-B).mutate 0).matrix i 1 = (-B).matrix i 1 := by
  rw [SkewExchangeMatrix.mutate_matrix]
  exact TauCeti.matrixMutation_apply_of_apply_row_eq_zero (by decide) (by
    rw [Function.Embedding.refl_apply, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply,
      exchangeMatrix, SkewExchangeMatrix.matrix_ofMatrix]
    decide) i

private theorem inverted_mutate_zero_row_one (i : I) :
    ((-B).mutate 0).matrix 1 i = (-B).matrix 1 i := by
  rw [SkewExchangeMatrix.apply_swap _ i 1, inverted_mutate_zero_col_one,
    ← SkewExchangeMatrix.apply_swap]

private def inversionStep : B ⟶ -B :=
  (Generator.invert.toStep B).cast rfl (Generator.target_invert B)

private def firstMutationStep : -B ⟶ (-B).mutate 0 :=
  ((Generator.mutate 0).toStep (-B)).cast rfl (Generator.target_mutate (-B) 0)

private def secondMutationStep : (-B).mutate 0 ⟶ B :=
  ((Generator.mutate 1).toStep ((-B).mutate 0)).cast rfl
    ((Generator.target_mutate _ _).trans mutate_inverted_twice)

private def swapStep : B ⟶ B :=
  ((Generator.permute τ).toStep B).cast rfl ((Generator.target_permute B τ).trans reindex_swap)

/-- The loop o, executing global inversion and then mutating at labels zero and one. -/
def oddWord : Word B B :=
  ((Path.nil.cons inversionStep).cons firstMutationStep).cons secondMutationStep

/-- The loop z, appending the transposition of the first two labels to o. -/
def involutionWord : Word B B := oddWord.cons swapStep

/-- The first loop has one inversion step. -/
@[simp]
theorem inversionCount_oddWord : oddWord.inversionCount = 1 := by
  simp [oddWord, inversionStep, firstMutationStep, secondMutationStep]

/-- Appending the transposition leaves the inversion count at one. -/
@[simp]
theorem inversionCount_involutionWord : involutionWord.inversionCount = 1 := by
  simp [involutionWord, swapStep]

/-- The three sums of the exponents over the three rays. -/
def raySum (x : I → ℤ) (r : Fin 3) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ rayIndex i = r), x i

/-- The two charge coordinates are differences of ray sums. -/
theorem chargeMap_apply (x : I → ℤ) :
    chargeMap x = ![raySum x 0 - raySum x 2, raySum x 1 - raySum x 2] := by
  simp only [chargeMap, Basis.constr_apply_fintype, raySum, Finset.sum_filter]
  ext j
  fin_cases j <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    simp [charge, rayIndex] <;> omega

/-- The charge lattice is generated by the labels on the first two rays. -/
theorem surjective_chargeMap : Function.Surjective chargeMap := by
  intro n
  refine ⟨Pi.single 0 (n 0) + Pi.single 2 (n 1), ?_⟩
  simp only [chargeMap_apply, raySum, Finset.sum_filter]
  ext j
  fin_cases j <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    simp [rayIndex]

/-- The exchange kernel is the charge kernel for this seed. -/
theorem exchangeKernel_eq_chargeKernel : (B).matrix.mulVecLin.ker = chargeMap.ker := by
  rw [exchangeMatrix_eq_chargeExchangeMatrix]
  apply ker_chargeExchangeMatrix
  · intro x hx
    funext j
    obtain ⟨y, hy⟩ := (det₂).surjective (LinearMap.proj j)
    exact (DFunLike.congr_fun hy x).symm.trans (hx y)
  · rw [LinearMap.range_eq_top.mpr surjective_chargeMap, finrank_top]

/-- An exponent is a Casimir exponent exactly when its three ray sums coincide. -/
theorem mem_exchangeKernel_iff (x : I → ℤ) :
    x ∈ (B).matrix.mulVecLin.ker ↔ raySum x 0 = raySum x 1 ∧ raySum x 1 = raySum x 2 := by
  rw [exchangeKernel_eq_chargeKernel, LinearMap.mem_ker, chargeMap_apply]
  constructor
  · intro h
    have h₀ : raySum x 0 - raySum x 2 = 0 := congrFun h 0
    have h₁ : raySum x 1 - raySum x 2 = 0 := congrFun h 1
    omega
  · rintro ⟨h₀, h₁⟩
    funext j
    fin_cases j <;> simp [h₀, h₁]

/-- The vector with exponents three, two and one on the successive rays. -/
def boundaryExponent : I → ℤ := fun i ↦ (![3, 2, 1] : Fin 3 → ℤ) (rayIndex i)

/-- The boundary exponent is three, two or one according to the ray index. -/
theorem boundaryExponent_apply (i : I) :
    boundaryExponent i = (![3, 2, 1] : Fin 3 → ℤ) (rayIndex i) :=
  (rfl)

/-- The boundary exponent has charge zero. -/
theorem boundaryExponent_mem_exchangeKernel : boundaryExponent ∈ (B).matrix.mulVecLin.ker :=
  (mem_exchangeKernel_iff _).mpr (by decide)

/-- The boundary exponent is primitive in the ambient exponent lattice. -/
theorem isPrimitive_boundaryExponent : TauCeti.IsPrimitive boundaryExponent :=
  TauCeti.isPrimitive_def.mpr ⟨LinearMap.proj 10, by decide⟩

/-- The sum over the first ray uses its two labels. -/
@[simp]
theorem raySum_zero (x : I → ℤ) : raySum x 0 = x 0 + x 1 := by
  rw [raySum, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [rayIndex]

/-- The sum over the second ray uses its three labels. -/
@[simp]
theorem raySum_one (x : I → ℤ) : raySum x 1 = x 2 + x 3 + x 4 := by
  rw [raySum, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [rayIndex, add_assoc]

/-- The sum over the last ray uses its six labels. -/
@[simp]
theorem raySum_two (x : I → ℤ) :
    raySum x 2 = x 5 + x 6 + x 7 + x 8 + x 9 + x 10 := by
  rw [raySum, Finset.sum_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [rayIndex, add_assoc]

private theorem neg_exchangeMatrix_column (k : I) (hk : rayIndex k = 0) (i : I) :
    (-B).matrix i k = if rayIndex i = 0 then 0 else if rayIndex i = 1 then 1 else -1 := by
  simp only [SkewExchangeMatrix.neg_matrix, Matrix.neg_apply, exchangeMatrix,
    SkewExchangeMatrix.matrix_ofMatrix, Matrix.submatrix_apply, hk]
  generalize rayIndex i = j
  fin_cases j <;> decide

private theorem chargeMutationEquiv_pivot (k : I) (hk : rayIndex k = 0) (x : I → ℤ) :
    chargeMutationEquiv (-B).matrix k x k = -x k + raySum x 1 := by
  rw [chargeMutationEquiv_apply_self, raySum, Finset.sum_filter]
  congr 1
  have hcoeff (i : I) : (-(-B).matrix k i)⁺ * x i = if rayIndex i = 1 then x i else 0 := by
    rw [SkewExchangeMatrix.apply_swap _ i k, neg_neg, neg_exchangeMatrix_column k hk i]
    generalize rayIndex i = j
    fin_cases j <;> simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  simp only [hcoeff, hk, zero_ne_one, ite_false, add_zero]

/-- The first odd word negates the Casimir exponents and exchanges the two labels
on the first ray. -/
theorem oddWord_exchangeKernelEquiv (x : (B).matrix.mulVecLin.ker) :
    (oddWord.exchangeKernelEquiv x : I → ℤ) = fun i ↦ -x.val (τ i) := by
  have hx : raySum x.val 1 = x.val 0 + x.val 1 :=
    ((mem_exchangeKernel_iff _).mp x.property).1.symm.trans (raySum_zero _)
  have hrow : ((-B).mutate 0).matrix 1 = (-B).matrix 1 :=
    funext inverted_mutate_zero_row_one
  have hsecond (y : I → ℤ) :
      chargeMutationEquiv ((-B).mutate 0).matrix 1 y 1 = -y 1 + raySum y 1 := by
    rw [chargeMutationEquiv_apply_self, hrow,
      ← chargeMutationEquiv_apply_self (-B).matrix]
    exact chargeMutationEquiv_pivot 1 (by decide) y
  funext i
  simp only [Path.coe_exchangeKernelEquiv_apply, oddWord, Path.exponentEquiv_cons,
    Path.exponentEquiv_nil, inversionStep, firstMutationStep, secondMutationStep,
    Step.exponentEquiv_cast, Step.exponentEquiv_invert, Step.exponentEquiv_mutate,
    LinearEquiv.trans_apply, LinearEquiv.refl_apply, LinearEquiv.neg_apply, Pi.neg_apply]
  rcases eq_or_ne i 0 with rfl | h₀
  · rw [chargeMutationEquiv_pivot 0 (by decide),
      chargeMutationEquiv_apply_of_ne _ (show (0 : I) ≠ 1 by decide),
      raySum_one, chargeMutationEquiv_apply_of_ne _ (show (2 : I) ≠ 1 by decide),
      chargeMutationEquiv_apply_of_ne _ (show (3 : I) ≠ 1 by decide),
      chargeMutationEquiv_apply_of_ne _ (show (4 : I) ≠ 1 by decide), ← raySum_one, hx]
    simp
  · rcases eq_or_ne i 1 with rfl | h₁
    · rw [chargeMutationEquiv_apply_of_ne _ (show (1 : I) ≠ 0 by decide), hsecond, hx]
      simp
    · rw [chargeMutationEquiv_apply_of_ne _ h₀, chargeMutationEquiv_apply_of_ne _ h₁,
        Equiv.swap_apply_of_ne_of_ne h₀ h₁]

/-- The word with the additional transposition is negation on the exchange kernel. -/
@[simp]
theorem involutionWord_exchangeKernelEquiv_apply (x : (B).matrix.mulVecLin.ker) :
    involutionWord.exchangeKernelEquiv x = -x := by
  have hx := (SetLike.ext_iff.mp (Step.exchangeKernel_comap swapStep) x.val).mp x.property
  let y : (B).matrix.mulVecLin.ker :=
    ⟨Step.exponentEquiv swapStep x.val, Submodule.mem_comap.mp hx⟩
  apply Subtype.ext
  rw [Path.coe_exchangeKernelEquiv_apply, involutionWord, Path.exponentEquiv_cons,
    LinearEquiv.trans_apply]
  rw [← Path.coe_exchangeKernelEquiv_apply oddWord y, oddWord_exchangeKernelEquiv]
  funext i
  simp [y, swapStep, LinearEquiv.funCongrLeft_apply]

section Pullback

variable (k : Type*) [Field k]

local notation "X[" i "]" => xCoordinate k (ι := I) i
local notation "P" => (1 + X[0]) * (1 + X[1])

private theorem one_add_inv_xCoordinate (i : I) :
    1 + (X[i])⁻¹ = (1 + X[i]) / X[i] := by
  rw [add_div, one_div, div_self (xCoordinate_ne_zero k i), add_comm]

/-- The first odd loop fixes the first two X coordinates and acts by scaled inversion
on the two other blocks. -/
theorem oddWord_xPullback_xCoordinate (i : I) :
    oddWord.xPullback k (X[i]) =
      if i = 0 ∨ i = 1 then X[i]
      else if rayIndex i = 1 then (X[i])⁻¹ / P
      else (X[i])⁻¹ * P / (X[0] * X[1]) := by
  have h₀ : rayIndex 0 = 0 := by decide
  have h₁ : rayIndex 1 = 0 := by decide
  have h01 : (0 : I) ≠ 1 := by decide
  have h10 : (1 : I) ≠ 0 := by decide
  simp only [oddWord, Path.xPullback_cons, Path.xPullback_nil, one_mul, AlgEquiv.mul_apply,
    Step.xPullback_eq, inversionStep, firstMutationStep, secondMutationStep, Step.generator_cast,
    Generator.toStep_generator, Generator.xPullback_invert, Generator.xPullback_mutate,
    inverted_mutate_zero_col_one, neg_exchangeMatrix_column 0 h₀, neg_exchangeMatrix_column 1 h₁]
  rcases eq_or_ne i 0 with rfl | hi₀
  · simp [h₀, xMutation_apply_of_ne, h01]
  · rcases eq_or_ne i 1 with rfl | hi₁
    · simp [h₁, xMutation_apply_of_ne, h10]
    · rw [xMutation_apply_of_ne k 1 _ hi₁]
      simp only [map_mul, map_zpow₀, map_add, map_one]
      rw [xMutation_apply_of_ne k 0 _ hi₀, xMutation_apply_of_ne k 0 _ h10]
      simp only [h₁, ite_true, max_self, zpow_zero, mul_one, neg_zero, hi₀, hi₁,
        or_false, ite_false]
      have h : rayIndex i ≠ 0 := mt (rayIndex_eq_zero_iff i).mp (not_or.mpr ⟨hi₀, hi₁⟩)
      by_cases h' : rayIndex i = 1
      · simp [h', zpow_neg, one_add_inv_xCoordinate]
        field_simp
      · simp [h, h', one_add_inv_xCoordinate]
        field_simp

/-- The second odd loop exchanges the first two X coordinates. On the second ray it
divides the reciprocal by the product of the two mutation binomials. On the third ray
it multiplies the reciprocal by that product divided by the two pivot coordinates. -/
theorem involutionWord_xPullback_xCoordinate (i : I) :
    involutionWord.xPullback k (X[i]) =
      if i = 0 ∨ i = 1 then X[τ i]
      else if rayIndex i = 1 then (X[i])⁻¹ / P
      else (X[i])⁻¹ * P / (X[0] * X[1]) := by
  simp only [involutionWord, Path.xPullback_cons, AlgEquiv.mul_apply, Step.xPullback_eq,
    swapStep, Step.generator_cast, Generator.toStep_generator, Generator.xPullback_permute,
    xReindex_apply_xCoordinate, oddWord_xPullback_xCoordinate]
  rcases eq_or_ne i 0 with rfl | h₀
  · simp
  · rcases eq_or_ne i 1 with rfl | h₁
    · simp
    · simp [Equiv.swap_apply_of_ne_of_ne h₀ h₁]

/-- The pullback of the first coordinate is the second. -/
@[simp]
theorem involutionWord_xPullback_xCoordinate_zero :
    involutionWord.xPullback k (X[0]) = X[1] := by
  simp [involutionWord_xPullback_xCoordinate]

/-- The pullback of the second coordinate is the first. -/
@[simp]
theorem involutionWord_xPullback_xCoordinate_one :
    involutionWord.xPullback k (X[1]) = X[0] := by
  simp [involutionWord_xPullback_xCoordinate]

/-- The square of the rational transformation of z fixes every independent X coordinate. -/
theorem involutionWord_xPullback_sq : involutionWord.xPullback k ^ 2 = 1 := by
  rw [pow_two]
  apply algEquiv_ext_xCoordinate k
  intro i
  simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  rcases eq_or_ne i 0 with rfl | h₀
  · simp
  · rcases eq_or_ne i 1 with rfl | h₁
    · simp
    · have h := involutionWord_xPullback_xCoordinate k i
      simp only [h₀, h₁, or_self, ite_false] at h
      by_cases hi : rayIndex i = 1
      · rw [ite_eq_left hi] at h
        rw [h]
        simp only [map_div₀, map_inv₀, map_mul, map_add, map_one,
          involutionWord_xPullback_xCoordinate_zero, involutionWord_xPullback_xCoordinate_one, h]
        field_simp
      · rw [ite_eq_right hi] at h
        rw [h]
        simp only [map_div₀, map_inv₀, map_mul, map_add, map_one,
          involutionWord_xPullback_xCoordinate_zero, involutionWord_xPullback_xCoordinate_one, h]
        field_simp [mul_ne_zero]

/-- The interchange of the first two independent coordinates makes z nontrivial. -/
theorem involutionWord_xPullback_ne_one : involutionWord.xPullback k ≠ 1 := by
  intro h
  have h₀ : X[1] = X[0] := by
    simpa only [involutionWord_xPullback_xCoordinate_zero, AlgEquiv.one_apply] using
      DFunLike.congr_fun h (X[0])
  simp only [xCoordinate_def] at h₀
  exact (by decide : (1 : I) ≠ 0) <|
    Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) <|
    AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0) <|
    IsFractionRing.injective _ _ h₀

/-- Over any coefficient field, the X pullback of z is an involution of order exactly two. -/
theorem orderOf_involutionWord_xPullback : orderOf (involutionWord.xPullback k) = 2 :=
  orderOf_eq_prime (involutionWord_xPullback_sq k) (involutionWord_xPullback_ne_one k)

end Pullback

end QPainleve.ElevenVertex
