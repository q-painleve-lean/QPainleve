/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.Algebra.Cluster.Tropical.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

import QPainleve.Algebra.Cluster.Word.Commute

/-!
# The four-vertex cluster words of type A₇⁽¹⁾′

The signed loop `π₁`, the rotation `π₂`, and the translation `T` act on the integer
exchange kernel of the doubled oriented square. The kernel coordinates are the exponents
on the first two vertices, with equal exponents at opposite vertices.

The words are those of Bershtein, Gavrylenko and Marshakov, *Cluster integrable systems,
q-Painlevé equations and their quantization*, (3.1), expressed in the `X = y⁻¹` convention.
Vertex numbers in the file start at zero.
-/

public section

open Quiver
open scoped Matrix

namespace QPainleve.FourVertex

open Cluster

private def entries : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 2, 0, -2; -2, 0, 2, 0; 0, -2, 0, 2; 2, 0, -2, 0]

/-- The doubled oriented square in the cluster X exchange convention. -/
def exchangeMatrix : SkewExchangeMatrix (Fin 4) :=
  SkewExchangeMatrix.ofMatrix entries ⟨fun i ↦ by fin_cases i <;> decide,
    fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩

/-- The entries of the exchange matrix in cyclic vertex order. -/
theorem exchangeMatrix_matrix :
    exchangeMatrix.matrix = !![0, 2, 0, -2; -2, 0, 2, 0; 0, -2, 0, 2; 2, 0, -2, 0] :=
  SkewExchangeMatrix.matrix_ofMatrix _ _

local notation "B" => exchangeMatrix
local notation "σ" => (Equiv.symm (finRotate 4))
local notation "τ" => Equiv.swap (0 : Fin 4) 2
local notation "ρ" => Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3

private theorem rotation_target : (Generator.permute σ).target B = B := by
  apply SkewExchangeMatrix.ext
  ext i j
  simp only [Generator.target_permute, SkewExchangeMatrix.reindex_matrix,
    Matrix.submatrix_apply, Equiv.symm_symm, exchangeMatrix_matrix]
  fin_cases i <;> fin_cases j <;> decide

private theorem reflection_target : (Generator.permute τ).target (-B) = B := by
  apply SkewExchangeMatrix.ext
  ext i j
  simp only [Generator.target_permute, SkewExchangeMatrix.reindex_matrix,
    Matrix.submatrix_apply, Equiv.symm_symm, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply,
    exchangeMatrix_matrix]
  fin_cases i <;> fin_cases j <;> decide

private theorem mutate_zero_mutate_two : ((B).mutate 0).mutate 2 = -B := by
  apply SkewExchangeMatrix.ext
  ext i j
  simp only [SkewExchangeMatrix.mutate_matrix, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply,
    exchangeMatrix_matrix, TauCeti.matrixMutation_apply, Function.Embedding.coe_refl, id_eq]
  fin_cases i <;> fin_cases j <;> decide

private theorem translation_target :
    (Generator.permute ρ).target (((B).mutate 0).mutate 2) = B := by
  rw [mutate_zero_mutate_two]
  apply SkewExchangeMatrix.ext
  ext i j
  simp only [Generator.target_permute, SkewExchangeMatrix.reindex_matrix,
    Matrix.submatrix_apply, Equiv.symm_symm, SkewExchangeMatrix.neg_matrix, Matrix.neg_apply,
    exchangeMatrix_matrix]
  fin_cases i <;> fin_cases j <;> decide

/-- The loop `π₂`, which pulls each label back to its predecessor in the four-cycle. -/
def rotationWord : Word B B :=
  Path.nil.cons ⟨Generator.permute σ, rotation_target⟩

/-- The loop `T`, executing mutations at vertices zero and two followed by
the relabeling that swaps zero with one and two with three. -/
def translationWord : Word B B :=
  ((Path.nil.cons
    (⟨Generator.mutate 0, Generator.target_mutate B 0⟩ : Step B ((B).mutate 0))).cons
    (⟨Generator.mutate 2, Generator.target_mutate ((B).mutate 0) 2⟩ :
      Step ((B).mutate 0) (((B).mutate 0).mutate 2))).cons
    ⟨Generator.permute ρ, translation_target⟩

/-- The odd loop `π₁`, executing simultaneous inversion followed by the swap of zero and two. -/
def reflectionWord : Word B B :=
  (Path.nil.cons (⟨Generator.invert, Generator.target_invert B⟩ : Step B (-B))).cons
    ⟨Generator.permute τ, reflection_target⟩

@[simp]
theorem inversionCount_rotationWord : rotationWord.inversionCount = 0 := by
  simp [rotationWord]

@[simp]
theorem inversionCount_translationWord : translationWord.inversionCount = 0 := by
  simp [translationWord]

@[simp]
theorem inversionCount_reflectionWord : reflectionWord.inversionCount = 1 := by
  simp [reflectionWord]

/-- An exponent is in the exchange kernel exactly when its opposite entries agree. -/
theorem mem_exchangeKernel_iff (x : Fin 4 → ℤ) :
    x ∈ (B).matrix.mulVecLin.ker ↔ x 0 = x 2 ∧ x 1 = x 3 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, exchangeMatrix_matrix]
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h₀ h₁
    omega
  · rintro ⟨h₀, h₁⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h₀, h₁]

/-- The two independent exponents of a Casimir monomial, extended to all four vertices. -/
def exchangeKernelEquiv : (Fin 2 → ℤ) ≃ₗ[ℤ] (B).matrix.mulVecLin.ker where
  toFun x := ⟨![x 0, x 1, x 0, x 1], (mem_exchangeKernel_iff _).2 ⟨rfl, rfl⟩⟩
  invFun x := ![x.val 0, x.val 1]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    have ⟨h₀, h₁⟩ := (mem_exchangeKernel_iff _).1 x.property
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact h₀
    · exact h₁
  map_add' x y := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

@[simp]
theorem coe_exchangeKernelEquiv_apply (x : Fin 2 → ℤ) :
    (exchangeKernelEquiv x : Fin 4 → ℤ) = ![x 0, x 1, x 0, x 1] :=
  (rfl)

@[simp]
theorem exchangeKernelEquiv_symm_apply (x : (B).matrix.mulVecLin.ker) :
    exchangeKernelEquiv.symm x = ![x.val 0, x.val 1] :=
  (rfl)

/-- The rotation exchanges the two independent Casimir exponents. -/
@[simp]
theorem rotationWord_exchangeKernelEquiv (x : Fin 2 → ℤ) :
    rotationWord.exchangeKernelEquiv (exchangeKernelEquiv x) =
      exchangeKernelEquiv ![x 1, x 0] := by
  apply Subtype.ext
  funext i
  simp only [Path.coe_exchangeKernelEquiv_apply, rotationWord, Path.exponentEquiv_cons,
    Path.exponentEquiv_nil, Step.exponentEquiv_eq]
  fin_cases i <;> rfl

/-- The reflection negates both Casimir exponents. -/
@[simp]
theorem reflectionWord_exchangeKernelEquiv (x : Fin 2 → ℤ) :
    reflectionWord.exchangeKernelEquiv (exchangeKernelEquiv x) = exchangeKernelEquiv (-x) := by
  apply Subtype.ext
  funext i
  simp only [Path.coe_exchangeKernelEquiv_apply, reflectionWord, Path.exponentEquiv_cons,
    Path.exponentEquiv_nil, Step.exponentEquiv_eq]
  fin_cases i <;> rfl

/-- The half-turn fixes every Casimir exponent. -/
theorem rotationWord_comp_rotationWord_exchangeKernelEquiv :
    (rotationWord.comp rotationWord).exchangeKernelEquiv = 1 := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := exchangeKernelEquiv.surjective y
  rw [Path.exchangeKernelEquiv_comp, LinearEquiv.trans_apply,
    rotationWord_exchangeKernelEquiv, rotationWord_exchangeKernelEquiv, one_apply_eq_self]
  apply congrArg exchangeKernelEquiv
  funext i
  fin_cases i <;> rfl

private theorem mutate_zero_matrix_col_two (i : Fin 4) :
    ((B).mutate 0).matrix i 2 = (B).matrix i 2 := by
  rw [SkewExchangeMatrix.mutate_matrix]
  exact TauCeti.matrixMutation_apply_of_apply_row_eq_zero (by decide)
    (by rw [Function.Embedding.refl_apply, exchangeMatrix_matrix]; rfl) i

private theorem mutate_zero_matrix_row_two (i : Fin 4) :
    ((B).mutate 0).matrix 2 i = (B).matrix 2 i := by
  rw [SkewExchangeMatrix.apply_swap _ i 2, mutate_zero_matrix_col_two,
    ← SkewExchangeMatrix.apply_swap]

private theorem chargeMutationEquiv_two (x : Fin 4 → ℤ) :
    chargeMutationEquiv ((B).mutate 0).matrix 2 x = ![x 0, x 1, -x 2 + 2 * x 1, x 3] := by
  have h : (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} := by decide
  funext i
  fin_cases i
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _
  · have hp := chargeMutationEquiv_apply_self ((B).mutate 0).matrix 2 x
    rw [h] at hp
    simpa [mutate_zero_matrix_row_two, exchangeMatrix_matrix, posPart_def] using hp
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _

private theorem chargeMutationEquiv_zero (x : Fin 4 → ℤ) :
    chargeMutationEquiv (B).matrix 0 x = ![-x 0 + 2 * x 3, x 1, x 2, x 3] := by
  have h : (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide
  funext i
  fin_cases i
  · have hp := chargeMutationEquiv_apply_self (B).matrix 0 x
    rw [h] at hp
    simpa [exchangeMatrix_matrix, posPart_def] using hp
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _
  · exact chargeMutationEquiv_apply_of_ne _ (by decide) _

/-- In Casimir coordinates the pullback by `T` sends `(a,b)` to `(2a-b,a)`.
In particular it adds the all-ones exponent to the first basis vector and fixes
the all-ones exponent. -/
@[simp]
theorem translationWord_exchangeKernelEquiv (x : Fin 2 → ℤ) :
    translationWord.exchangeKernelEquiv (exchangeKernelEquiv x) =
      exchangeKernelEquiv ![2 * x 0 - x 1, x 0] := by
  apply Subtype.ext
  simp only [Path.coe_exchangeKernelEquiv_apply, translationWord, Path.exponentEquiv_cons,
    Path.exponentEquiv_nil, Step.exponentEquiv_eq, LinearEquiv.trans_apply, LinearEquiv.refl_apply]
  have hpermutation :
      LinearEquiv.funCongrLeft ℤ ℤ (Equiv.symm ρ) ![x 0, x 1, x 0, x 1] =
        ![x 1, x 0, x 1, x 0] := by
    funext i
    fin_cases i <;> rfl
  rw [coe_exchangeKernelEquiv_apply, coe_exchangeKernelEquiv_apply,
    hpermutation, chargeMutationEquiv_two, chargeMutationEquiv_zero]
  funext i
  fin_cases i <;> simp
  all_goals omega

section Pullback

variable (k : Type*) [Field k]

local notation "X[" i "]" => xCoordinate k (ι := Fin 4) i

/-- The rotation sends each X coordinate to the coordinate at its predecessor. -/
@[simp]
theorem rotationWord_xPullback_xCoordinate (i : Fin 4) :
    rotationWord.xPullback k (X[i]) = X[i - 1] := by
  simp [rotationWord, Step.xPullback_eq, finRotate_symm_apply]

/-- The square of the rotation exchanges opposite X coordinates. -/
theorem rotationWord_comp_rotationWord_xPullback_xCoordinate (i : Fin 4) :
    (rotationWord.comp rotationWord).xPullback k (X[i]) = X[i + 2] := by
  simp only [Path.xPullback_comp, AlgEquiv.mul_apply, rotationWord_xPullback_xCoordinate]
  congr 1
  exact (show ∀ j : Fin 4, j - 1 - 1 = j + 2 from by decide) i

/-- The reflection exchanges vertices zero and two and takes reciprocals. -/
@[simp]
theorem reflectionWord_xPullback_xCoordinate (i : Fin 4) :
    reflectionWord.xPullback k (X[i]) = (X[τ i])⁻¹ := by
  simp [reflectionWord, Step.xPullback_eq]

/-- In the independent cluster coordinates, the translation is the two-pivot
rational transformation with reciprocal coordinates at the two mutated vertices. -/
theorem translationWord_xPullback_xCoordinate :
    (fun i ↦ translationWord.xPullback k (X[i])) =
      ![X[1] * (1 + X[0]) ^ (2 : ℤ) * (1 + (X[2])⁻¹) ^ (-2 : ℤ), (X[0])⁻¹,
        X[3] * (1 + X[2]) ^ (2 : ℤ) * (1 + (X[0])⁻¹) ^ (-2 : ℤ), (X[2])⁻¹] := by
  simp only [translationWord, Path.xPullback_cons, Path.xPullback_nil, one_mul, AlgEquiv.mul_apply,
    Step.xPullback_eq, Generator.xPullback_permute, Generator.xPullback_mutate,
    xReindex_apply_xCoordinate]
  have hρ (i : Fin 4) : ρ i = (![1, 0, 3, 2] : Fin 4 → Fin 4) i := by
    fin_cases i <;> rfl
  funext i
  rw [hρ]
  have hbinomial (j : Fin 4) : 1 + (X[j])⁻¹ = (1 + X[j]) / X[j] := by
    rw [div_eq_mul_inv, add_mul, one_mul, mul_inv_cancel₀ (xCoordinate_ne_zero k j), add_comm]
  fin_cases i <;>
    norm_num [xMutation_apply_of_ne, mutate_zero_matrix_col_two, exchangeMatrix_matrix,
      map_mul, map_add, map_zpow, map_pow]
  all_goals
    rw [hbinomial, div_pow, inv_div, div_eq_mul_inv]
    simp only [mul_assoc, mul_left_comm, mul_comm]

/-- The translation pullback agrees with the order in (3.1): mutate the third vertex,
then the first, then swap the first pair and the last pair. Lean labels start at zero. -/
theorem translationWord_xPullback_mutate_two_first :
    translationWord.xPullback k =
      (Generator.mutate 2).xPullback k B * (Generator.mutate 0).xPullback k ((B).mutate 2) *
        (Generator.permute ρ).xPullback k (((B).mutate 2).mutate 0) := by
  simp only [translationWord, Path.xPullback_cons, Path.xPullback_nil, one_mul, Step.xPullback_eq]
  rw [Generator.xPullback_mutate_mul_mutate_comm k B (by rw [exchangeMatrix_matrix]; rfl)]
  simp only [Generator.xPullback_permute]

/-- The half-turn is nontrivial on the field of independent X coordinates. -/
theorem rotationWord_comp_rotationWord_xPullback_ne_one :
    (rotationWord.comp rotationWord).xPullback k ≠ 1 := by
  intro h
  have h₀ : (rotationWord.comp rotationWord).xPullback k (X[0]) = X[0] :=
    congrArg (fun f : _ ≃ₐ[k] _ ↦ f (X[0])) h
  rw [rotationWord_comp_rotationWord_xPullback_xCoordinate, Fin.zero_add] at h₀
  simp only [xCoordinate_def] at h₀
  exact (by decide : (2 : Fin 4) ≠ 0) <|
    Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) <|
    AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : k) ≠ 0) <|
    IsFractionRing.injective _ _ h₀

/-- The translation has infinite order in the signed cluster modular group. -/
theorem not_isOfFinOrder_translationWord :
    ¬ IsOfFinOrder (signedClusterModularGroupMap k B (CategoryTheory.End.of translationWord)) := by
  let g := signedClusterModularGroupMap k B (CategoryTheory.End.of translationWord)
  let A := exchangeKernelAction k B (MulOpposite.op g)
  have hA : A = translationWord.exchangeKernelEquiv := exchangeKernelAction_op_loop k B _
  have hpow (n : ℕ) :
      (A ^ n) (exchangeKernelEquiv ![1, 0]) = exchangeKernelEquiv ![1 + (n : ℤ), (n : ℤ)] := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, hA, translationWord_exchangeKernelEquiv]
      congr 1
      funext i
      fin_cases i <;> simp <;> omega
  intro hg
  obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
  have hAn : A ^ n = 1 := by
    rw [← map_pow, ← MulOpposite.op_pow, he, MulOpposite.op_one, map_one]
  have hcoeff := exchangeKernelEquiv.injective
    ((hpow n).symm.trans (congrArg (fun f ↦ f (exchangeKernelEquiv ![1, 0])) hAn))
  have hlast := congrFun hcoeff 1
  simp at hlast
  omega

end Pullback

/-- The primitive rays of the octagon obtained by subdividing the four cones of the
product fan of two projective lines. The numbering starts at `(1,0)` and proceeds
counterclockwise. -/
def boundaryRay : Fin 8 → Fin 2 → ℤ :=
  ![![1, 0], ![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]]

/-- The ray coordinates in the numbered octagon. -/
theorem boundaryRay_eq :
    boundaryRay = ![![1, 0], ![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]] :=
  (rfl)

/-- The charges at the four diagonals of the octagon. -/
def chargeVector (i : Fin 4) : Fin 2 → ℤ :=
  boundaryRay ⟨2 * i.val + 1, by omega⟩

/-- The charge at label `i` is the primitive generator of ray `2i+1`. -/
theorem chargeVector_eq (i : Fin 4) :
    chargeVector i = boundaryRay ⟨2 * i.val + 1, by omega⟩ :=
  (rfl)

/-- The exchange entries are the determinants of the ordered charge vectors. -/
theorem exchangeMatrix_matrix_apply (i j : Fin 4) :
    (B).matrix i j =
      Matrix.det !![chargeVector i 0, chargeVector i 1; chargeVector j 0, chargeVector j 1] := by
  rw [exchangeMatrix_matrix, Matrix.det_fin_two_of]
  fin_cases i <;> fin_cases j <;> decide

/-- The X orders at an octagon ray, computed by pairing the charges with that ray
in the determinant convention. -/
def boundaryOrders (j : Fin 8) (i : Fin 4) : ℤ :=
  Matrix.det !![chargeVector i 0, chargeVector i 1; boundaryRay j 0, boundaryRay j 1]

/-- The order of coordinate `i` at ray `j` is the determinant of the charge and ray. -/
theorem boundaryOrders_apply (j : Fin 8) (i : Fin 4) :
    boundaryOrders j i =
      Matrix.det !![chargeVector i 0, chargeVector i 1; boundaryRay j 0, boundaryRay j 1] :=
  (rfl)

/-- The eight boundary rays have distinct X order vectors. -/
theorem boundaryOrders_injective : Function.Injective boundaryOrders := by
  intro i j h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp only [boundaryOrders, Matrix.det_fin_two_of] at h₀ h₁
  fin_cases i <;> fin_cases j <;> first | rfl | contradiction

open CategoryTheory in
/-- Rotation by `π₂` transports each X order vector two positions around the octagon. -/
theorem rotationWord_tropical_boundaryOrders (j : Fin 8) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))).map rotationWord)
      (boundaryOrders j) = boundaryOrders (j + 2) := by
  simp only [rotationWord, Equiv.toFun_as_coe, tropical_map_cons_apply, Paths.lift_nil,
    SingleObj.id_as_one, Equiv.Perm.one_apply, Step.tropical_apply]
  funext i
  simp only [Generator.tropical_permute_apply, boundaryOrders, Matrix.det_fin_two_of]
  fin_cases i <;> fin_cases j <;> decide

open CategoryTheory in
/-- On octagon order vectors the square of `π₂` is the half-turn. -/
theorem rotationWord_comp_rotationWord_tropical_boundaryOrders (j : Fin 8) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))).map
      (rotationWord.comp rotationWord)) (boundaryOrders j) = boundaryOrders (j + 4) := by
  let F := Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))
  refine (congrArg (fun e : Equiv.Perm (Fin 4 → ℤ) ↦ e (boundaryOrders j))
    (F.map_comp rotationWord rotationWord)).trans ?_
  rw [SingleObj.comp_as_mul, Equiv.Perm.mul_apply]
  have h (i : Fin 8) : DFunLike.coe (F := Equiv.Perm (Fin 4 → ℤ)) (F.map rotationWord)
      (boundaryOrders i) = boundaryOrders (i + 2) :=
    rotationWord_tropical_boundaryOrders i
  rw [h, h, add_assoc]
  rfl

open CategoryTheory in
/-- The tropical point action of `T` moves each octagon ray back two positions. -/
theorem translationWord_tropical_boundaryOrders (j : Fin 8) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))).map translationWord)
      (boundaryOrders j) = boundaryOrders (j - 2) := by
  simp only [translationWord, Equiv.toFun_as_coe, tropical_map_cons_apply, Paths.lift_nil,
    SingleObj.id_as_one, Equiv.Perm.one_apply, Step.tropical_apply]
  funext i
  simp only [Generator.tropical_permute_apply]
  fin_cases i <;>
    norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Generator.tropical_mutate_of_ne,
      mutate_zero_matrix_col_two, exchangeMatrix_matrix]
  all_goals revert j; decide

open CategoryTheory in
/-- The tropical point action of `π₁` reflects the octagon by `j ↦ 6 - j`. -/
theorem reflectionWord_tropical_boundaryOrders (j : Fin 8) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))).map reflectionWord)
      (boundaryOrders j) = boundaryOrders (6 - j) := by
  simp only [reflectionWord, Equiv.toFun_as_coe, tropical_map_cons_apply, Paths.lift_nil,
    SingleObj.id_as_one, Equiv.Perm.one_apply, Step.tropical_apply]
  funext i
  simp only [Generator.tropical_permute_apply, Generator.tropical_invert_apply]
  revert j i
  decide

end QPainleve.FourVertex
