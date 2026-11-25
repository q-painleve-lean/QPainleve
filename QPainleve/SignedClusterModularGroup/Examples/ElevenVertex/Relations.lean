/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.Geometry.Toric.Fan.Boundary.Valuation
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Model

/-!
# Integer invariants for the eleven-vertex seed

Equality of the three ray sums lets us recover the exponents at labels zero
and two from the other nine. We use the last free coordinate as the coefficient
of the total boundary exponent. This gives an integral Casimir basis and an
explicit invariant for the inversion–mutation–transposition loop.
-/

public section

open Matrix Module Quiver
open QPainleve.Cluster

namespace QPainleve.ElevenVertex

local notation "K" => exchangeMatrix.matrix.mulVecLin.ker

private def freeLabel : Fin 9 → Fin 11 := ![1, 3, 4, 5, 6, 7, 8, 9, 10]

private def readCoordinates : K →ₗ[ℤ] (Fin 9 → ℤ) :=
  LinearMap.pi fun j ↦
    ((LinearMap.proj (freeLabel j) : (Fin 11 → ℤ) →ₗ[ℤ] ℤ) -
      (if j = 8 then 0 else boundaryExponent (freeLabel j)) • LinearMap.proj 10).comp (K).subtype

private def completeCoordinates : (Fin 9 → ℤ) →ₗ[ℤ] (Fin 11 → ℤ) :=
  let p (j : Fin 9) := LinearMap.proj (R := ℤ) (φ := fun _ : Fin 9 ↦ ℤ) j
  let s := p 3 + p 4 + p 5 + p 6 + p 7
  LinearMap.pi fun j ↦
    ![s - p 0, p 0, s - p 1 - p 2, p 1, p 2, p 3, p 4, p 5, p 6, p 7, 0] j +
      boundaryExponent j • p 8

private theorem completeCoordinates_mem (y : Fin 9 → ℤ) : completeCoordinates y ∈ K := by
  rw [mem_exchangeKernel_iff, raySum_zero, raySum_one, raySum_two]
  constructor <;> norm_num [completeCoordinates, boundaryExponent_apply, rayIndex_eq_ite] <;> ring

private def exchangeKernelEquiv : K ≃ₗ[ℤ] (Fin 9 → ℤ) :=
  LinearEquiv.ofLinearMap readCoordinates
    (completeCoordinates.codRestrict K completeCoordinates_mem)
    (by
      apply LinearMap.ext
      intro y
      funext j
      fin_cases j <;>
        norm_num [readCoordinates, completeCoordinates, freeLabel, boundaryExponent_apply,
          rayIndex_eq_ite])
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext j
      obtain ⟨h₀, h₁⟩ := (mem_exchangeKernel_iff _).mp x.property
      rw [raySum_zero, raySum_one] at h₀
      rw [raySum_one, raySum_two] at h₁
      fin_cases j <;>
        norm_num [readCoordinates, completeCoordinates, freeLabel, boundaryExponent_apply,
          rayIndex_eq_ite] <;> omega)

/-- The integral Casimir basis. Its last vector is the total boundary exponent. -/
noncomputable def exchangeKernelBasis : Basis (Fin 9) ℤ K :=
  Basis.ofEquivFun exchangeKernelEquiv

/-- The basis coefficients are the free exponents after subtracting the
contribution of the total boundary exponent, whose coefficient is `x 10`. -/
theorem exchangeKernelBasis_repr_apply (x : K) (j : Fin 9) :
    let v : Fin 11 → ℤ := x
    let t := v 10
    exchangeKernelBasis.repr x j =
      ![v 1 - 3 * t, v 3 - 2 * t, v 4 - 2 * t, v 5 - t, v 6 - t, v 7 - t,
        v 8 - t, v 9 - t, t] j := by
  fin_cases j <;>
    norm_num [exchangeKernelBasis, exchangeKernelEquiv, readCoordinates, freeLabel,
      boundaryExponent_apply, rayIndex_eq_ite]

/-- The ambient integer columns of the basis, obtained by completing the nine standard
coordinate vectors. -/
def exchangeKernelBasisVectors (j : Fin 9) : Fin 11 → ℤ :=
  completeCoordinates (Pi.single j 1)

/-- The computable ambient columns are the vectors of the integral Casimir basis. -/
@[simp]
theorem coe_exchangeKernelBasis_apply (j : Fin 9) :
    (exchangeKernelBasis j : Fin 11 → ℤ) = exchangeKernelBasisVectors j := by
  rw [exchangeKernelBasis, Basis.coe_ofEquivFun]
  rfl

/-- The ninth basis vector is the total boundary exponent in the original labels. -/
@[simp]
theorem exchangeKernelBasisVectors_eight : exchangeKernelBasisVectors 8 = boundaryExponent := by
  funext j
  fin_cases j <;>
    norm_num [exchangeKernelBasisVectors, completeCoordinates, Pi.single_apply]

/-- The order table comes from the strict line with six centers, the ray that
survives both nodal contractions. -/
theorem rayBoundaryOrders_planeBoundaryRay_two :
    TauCeti.Toric.Fan.rayBoundaryOrders (Pi.basisFun ℤ (Fin 2))
      planeCenterRay (planeBoundaryRay 2) = boundaryOrders 0 := by
  funext i
  simp only [TauCeti.Toric.Fan.rayBoundaryOrders_apply_eq_repr, planeCenterRay_apply,
    primitiveGenerator_planeBoundaryRay, Pi.basisFun_repr, boundaryOrders_apply,
    ← rayIndex_eq_ite]
  generalize rayIndex i = j
  fin_cases j <;> decide

/-- The inversion–mutation–transposition word has negative sign, negates every
Casimir basis column, and returns the unique forward boundary label. -/
theorem involutionWord_signedLoopInvariants :
    involutionWord.signedLoopInvariants exchangeKernelBasisVectors boundaryOrders
      (boundaryOrders 0) = ⟨-1, -Matrix.of (fun i j ↦ exchangeKernelBasisVectors j i), some 0⟩ := by
  refine SignedLoopInvariants.ext ?_ ?_ ?_
  · simp [inversionCount_involutionWord]
  · ext i j
    simp only [Path.signedLoopInvariants_kernelColumns, Matrix.neg_apply, Matrix.of_apply,
      ← coe_exchangeKernelBasis_apply,
      ← Path.coe_exchangeKernelEquiv_apply, involutionWord_exchangeKernelEquiv_apply,
      Submodule.coe_neg, Pi.neg_apply]
  · exact (involutionWord.signedLoopInvariants_boundaryLabel_eq_some_iff _ _
      (Function.injective_of_subsingleton boundaryOrders) 0).mpr
      involutionWord_tropical_boundaryOrders.symm

end QPainleve.ElevenVertex
