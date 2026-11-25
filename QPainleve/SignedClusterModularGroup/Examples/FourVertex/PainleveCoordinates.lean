/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

/-!
# The four-vertex generators in Painlevé coordinates

These are the generators in [Bershtein, Gavrylenko and Marshakov][BGM],
(3.1)–(3.3), with reciprocal cluster coordinates `yᵢ = Xᵢ⁻¹`. The translation
can use the two nonadjacent mutations in either order. The Laurent change of
variables to `(Z, q, F, G)` is invertible on the field of independent coordinates.

[BGM]: https://doi.org/10.1007/JHEP02(2018)077
-/

public noncomputable section

open scoped Matrix

namespace QPainleve.FourVertex

open CharacterTorus Cluster

variable (k : Type*) [Field k]

local notation "X[" i "]" => xCoordinate k (ι := Fin 4) i
local notation "Y[" i "]" => (X[i])⁻¹

/-- Conjugating by `X = y⁻¹` gives the cyclic relabeling in (3.1). -/
theorem conj_xInversion_rotationWord_xPullback :
    MulAut.conj (xInversion k (Fin 4)) (rotationWord.xPullback k) =
      xReindex k (finRotate 4).symm := by
  apply algEquiv_ext_xCoordinate k
  intro i
  simp [MulAut.conj_apply, AlgEquiv.aut_inv, finRotate_symm_apply]

/-- Conjugating by `X = y⁻¹` gives the swap of the first and third labels followed by
inversion of all four variables, as in (3.1). -/
theorem conj_xInversion_reflectionWord_xPullback :
    MulAut.conj (xInversion k (Fin 4)) (reflectionWord.xPullback k) =
      xInversion k (Fin 4) * xReindex k (Equiv.swap 0 2) := by
  apply algEquiv_ext_xCoordinate k
  intro i
  simp [MulAut.conj_apply, AlgEquiv.aut_inv]

/-- The translation in the `y` coordinates is the rational map of (3.2). -/
theorem translationWord_xPullback_inv_xCoordinate :
    (fun i ↦ translationWord.xPullback k (Y[i])) =
      ![Y[1] * (1 + Y[2]) ^ 2 / (1 + (Y[0])⁻¹) ^ 2, (Y[0])⁻¹,
        Y[3] * (1 + Y[0]) ^ 2 / (1 + (Y[2])⁻¹) ^ 2, (Y[2])⁻¹] := by
  funext i
  rw [map_inv₀ (translationWord.xPullback k), congrFun (translationWord_xPullback_xCoordinate k) i]
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val, inv_inv, mul_inv_rev, zpow_neg, zpow_ofNat,
      div_eq_mul_inv]
  all_goals ring

private def painleveExponents : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, -1, 0; 1, -1, 0, 1; 0, -1, 0, 0; 1, -1, 0, 0]

private def inversePainleveExponents : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, -1, 1; 0, 0, -1, 0; -1, 0, 1, 0; 0, 1, 0, -1]

private noncomputable def painleveExponentEquiv : (Fin 4 →₀ ℤ) ≃ₗ[ℤ] (Fin 4 →₀ ℤ) :=
  Matrix.toLinOfInv Finsupp.basisSingleOne Finsupp.basisSingleOne
    (M := painleveExponents) (M' := inversePainleveExponents)
    (Matrix.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> decide)
    (Matrix.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> decide)

/-- The function-field change of coordinates whose pullback sends the four independent
variables, in order, to `Z = y₁⁻¹ y₃⁻¹`, `q = y₀ y₁ y₂ y₃`, `F = y₀`, and `G = y₁⁻¹`.
The subscripts here are zero-based. -/
def painleveCoordinateChange :
    FunctionField k (Fin 4 →₀ ℤ) ≃ₐ[k] FunctionField k (Fin 4 →₀ ℤ) :=
  IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k painleveExponentEquiv.toAddEquiv)

private theorem functionFieldMatrix_xCoordinate (e : (Fin 4 →₀ ℤ) ≃ₗ[ℤ] (Fin 4 →₀ ℤ))
    (M : Matrix (Fin 4) (Fin 4) ℤ)
    (h : e.toLinearMap = M.toLin Finsupp.basisSingleOne Finsupp.basisSingleOne) (i : Fin 4) :
    (IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k e.toAddEquiv) :
      FunctionField k (Fin 4 →₀ ℤ) ≃ₐ[k] FunctionField k (Fin 4 →₀ ℤ)) (X[i]) =
      ∏ j, X[j] ^ M j i := by
  have he : e (Finsupp.single i 1) = Finsupp.equivFunOnFinite.symm (M.col i) := by
    have hi : e (Finsupp.single i 1) =
        M.toLin Finsupp.basisSingleOne Finsupp.basisSingleOne (Finsupp.single i 1) :=
      LinearMap.congr_fun h _
    rw [hi]
    ext j
    have hh := Matrix.repr_toLin Finsupp.basisSingleOne Finsupp.basisSingleOne M
      (Finsupp.single i 1)
    simpa only [Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply,
      Finsupp.single_eq_pi_single, Matrix.mulVec_single_one, Finsupp.coe_equivFunOnFinite_symm]
      using congrFun hh j
  have he' : e.toAddEquiv (Finsupp.single i 1) = Finsupp.equivFunOnFinite.symm (M.col i) := he
  rw [xCoordinate_def, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    AddMonoidAlgebra.domCongr_single, ← monomial_ofAdd, he', monomial_eq_prod_zpow_xCoordinate]
  rfl

/-- The pullback of the Painlevé coordinates in terms of the four X coordinates. -/
@[simp]
theorem painleveCoordinateChange_xCoordinate (i : Fin 4) :
    painleveCoordinateChange k (X[i]) =
      ![X[1] * X[3], (X[0] * X[1] * X[2] * X[3])⁻¹, Y[0], X[1]] i := by
  rw [painleveCoordinateChange, functionFieldMatrix_xCoordinate k _ painleveExponents (rfl)]
  fin_cases i <;> simp [painleveExponents, Fin.prod_univ_four, mul_inv_rev, mul_assoc, mul_comm]

/-- The inverse substitution recovers each original X coordinate from `(Z, q, F, G)`. -/
@[simp]
theorem painleveCoordinateChange_symm_xCoordinate (i : Fin 4) :
    (painleveCoordinateChange k).symm (X[i]) =
      ![(X[2])⁻¹, X[3], X[2] / (X[1] * X[0]), X[0] / X[3]] i := by
  rw [painleveCoordinateChange, IsFractionRing.algEquivOfAlgEquiv_symm,
    AddMonoidAlgebra.domCongr_symm]
  have hinv : painleveExponentEquiv.toAddEquiv.symm = painleveExponentEquiv.symm.toAddEquiv := rfl
  rw [hinv, functionFieldMatrix_xCoordinate k _ inversePainleveExponents (rfl)]
  fin_cases i <;> simp [inversePainleveExponents, Fin.prod_univ_four, div_eq_mul_inv,
    mul_assoc, mul_comm]

local notation "Z" => X[0]
local notation "q" => X[1]
local notation "F" => X[2]
local notation "G" => X[3]
local notation "pullback[" w "]" =>
  AlgEquiv.trans (painleveCoordinateChange k)
    (AlgEquiv.trans (Quiver.Path.xPullback k w) (AlgEquiv.symm (painleveCoordinateChange k)))

/-- In the independent coordinates `(Z, q, F, G)`, rotation interchanges the two
Casimirs `(qZ, Z⁻¹)` and pulls the last coordinate back to `F⁻¹`. -/
theorem rotationWord_painleve_xCoordinate :
    (fun i ↦ pullback[rotationWord] (X[i])) = ![(q * Z)⁻¹, q, G / Z, F⁻¹] := by
  funext i
  apply (painleveCoordinateChange k).injective
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  have hneg : (-1 : Fin 4) = 3 := by decide
  fin_cases i <;>
    simp [div_eq_mul_inv,
      mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, hneg]

/-- The odd generator of (3.1) inverts the Casimirs. In the variables of (3.3),
it sends `F` to the reciprocal of the original third cluster coordinate, `F / (q * Z)`. -/
theorem reflectionWord_painleve_xCoordinate :
    (fun i ↦ pullback[reflectionWord] (X[i])) = ![Z⁻¹, q⁻¹, F / (q * Z), G⁻¹] := by
  funext i
  apply (painleveCoordinateChange k).injective
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  fin_cases i <;>
    simp [div_eq_mul_inv,
      mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, Equiv.swap_apply_def]

private theorem translationWord_xPullback_q :
    translationWord.xPullback k ((X[0] * X[1] * X[2] * X[3])⁻¹) =
      (X[0] * X[1] * X[2] * X[3])⁻¹ := by
  have h := translationWord.xPullback_apply_monomial k (exchangeKernelEquiv ![-1, -1])
  rw [translationWord_exchangeKernelEquiv] at h
  simpa [monomial_eq_prod_zpow_xCoordinate, Fin.prod_univ_four, mul_inv_rev,
    mul_assoc, mul_comm] using h

/-- The translation is the rational time evolution in the independent Painlevé
coordinates. It fixes `q`, sends `Z` to `qZ`, and sends `G` to `F`. -/
theorem translationWord_painleve_xCoordinate :
    (fun i ↦ pullback[translationWord] (X[i])) =
      ![q * Z, q, (F + q * Z) ^ 2 / ((F + 1) ^ 2 * G), F] := by
  funext i
  apply (painleveCoordinateChange k).injective
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  fin_cases i <;>
    simp only [Fin.reduceFinMk, Matrix.cons_val,
      painleveCoordinateChange_xCoordinate, map_mul, map_add, map_one, map_div₀,
      map_pow]
  · rw [congrFun (translationWord_xPullback_xCoordinate k) 1,
      congrFun (translationWord_xPullback_xCoordinate k) 3]
    simp only [Matrix.cons_val]
    field_simp
  · exact translationWord_xPullback_q k
  · rw [congrFun (translationWord_xPullback_inv_xCoordinate k) 0]
    simp only [Matrix.cons_val, inv_inv]
    have h : 1 + X[0]⁻¹ ≠ 0 := by
      simpa [map_add] using (xInversion k (Fin 4)).injective.ne
        (one_add_xCoordinate_ne_zero k 0)
    field_simp [h, add_comm]
  · exact congrFun (translationWord_xPullback_xCoordinate k) 1

end QPainleve.FourVertex
