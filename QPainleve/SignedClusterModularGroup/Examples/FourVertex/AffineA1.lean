/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Basic
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling

/-!
# The affine A₁ lattice of the four-vertex seed

In the four-vertex Picard marking, the two alternating pairs of internal
exceptional classes give the simple-root coordinates of the boundary orthogonal
lattice. The same coordinates give the two independent Casimir exponents.
The total boundary is the sum of the two simple roots.

The comparison uses Tau Ceti's integral-form rationalization and
`IntegralLattice.Isometry.ofGramMatrixEq`.
-/

public noncomputable section

open LinearMap Module Submodule TauCeti.IntegralLattice
open scoped TensorProduct

namespace QPainleve.FourVertex

local notation "K" => intersectionForm.orthogonal (span ℤ (Set.range boundaryClass))
local notation "B" => intersectionForm.restrict K
local notation "hB" => intersectionForm_isSymm.restrict K
local notation "L" => ofIntegralForm B hB
local notation "A" => (-affineA1 : TauCeti.IntegralLattice (Fin 2 → ℚ))
local notation "E" => exchangeMatrix.matrix.mulVecLin.ker

private theorem affineCarrier_eq :
    (A).carrier = span ℤ (Set.range (Pi.basisFun ℚ (Fin 2))) := by
  ext x
  rw [neg_carrier, mem_affineA1_carrier_iff, Basis.mem_span_iff_repr_mem]
  simp [Pi.basisFun_repr]

private def affineBasis : Basis (Fin 2) ℤ A :=
  ((Pi.basisFun ℚ (Fin 2)).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ affineCarrier_eq.symm)

private theorem coe_affineBasis (i : Fin 2) :
    (affineBasis i : Fin 2 → ℚ) = Pi.single i 1 := by
  rw [affineBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.restrictScalars_apply, Pi.basisFun_apply]

private theorem gramMatrix_boundaryOrthogonal_eq :
    (L).gramMatrix (boundaryOrthogonalBasis.map (ofIntegralForm.carrierEquiv B hB)) =
      (A).gramMatrix affineBasis := by
  ext i j
  rw [gramMatrix_apply, gramMatrix_apply, Basis.map_apply, Basis.map_apply,
    ofIntegralForm.integralForm_carrierEquiv]
  apply Int.cast_injective (α := ℚ)
  simp only [integralForm_cast, neg_form, LinearMap.neg_apply, affineA1_form_apply,
    coe_affineBasis, BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  rw [intersectionForm_boundaryOrthogonalBasis]
  fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

/-- The rationalized Picard orthogonal lattice of the four-vertex marking is
isometric to negative affine `A₁`, matching the two alternating exceptional
pairs with the two simple roots in their displayed order. -/
def boundaryOrthogonalIsometryNegAffineA1 : Isometry L A :=
  Isometry.ofGramMatrixEq _ _ gramMatrix_boundaryOrthogonal_eq

/-- The native isometry sends the integral Picard basis to the standard simple roots. -/
@[simp]
theorem boundaryOrthogonalIsometryNegAffineA1_tmul_basis (i : Fin 2) :
    boundaryOrthogonalIsometryNegAffineA1 (1 ⊗ₜ[ℤ] boundaryOrthogonalBasis i) = Pi.single i 1 := by
  rw [boundaryOrthogonalIsometryNegAffineA1]
  simpa only [Basis.map_apply, ofIntegralForm.coe_carrierEquiv_apply, coe_affineBasis] using
    (Isometry.ofGramMatrixEq_apply_basis _ _ gramMatrix_boundaryOrthogonal_eq i)

/-- The image of an integral Picard vector has its two boundary-orthogonal basis
coefficients as coordinates in the standard affine `A₁` lattice. -/
theorem boundaryOrthogonalIsometryNegAffineA1_apply_tmul (x : K) :
    boundaryOrthogonalIsometryNegAffineA1 (1 ⊗ₜ[ℤ] x) =
      fun j ↦ ((boundaryOrthogonalBasis.repr x j : ℤ) : ℚ) := by
  let e := (ofIntegralForm.carrierEquiv B hB).trans
    boundaryOrthogonalIsometryNegAffineA1.carrierEquiv
  have h := congrArg (fun y : K ↦ (e y : Fin 2 → ℚ)) (boundaryOrthogonalBasis.sum_repr x)
  rw [map_sum] at h
  simp only [Submodule.coe_sum, map_smul, Submodule.coe_smul, e, LinearEquiv.trans_apply,
    Isometry.coe_carrierEquiv_apply, ofIntegralForm.coe_carrierEquiv_apply,
    boundaryOrthogonalIsometryNegAffineA1_tmul_basis] at h
  funext j
  simpa [Finset.sum_apply, Pi.single_apply] using (congrFun h j).symm

/-- The coefficients on the Picard orthogonal lattice are the independent Casimir
exponents. This identifies the Picard basis with the alternating exponent pairs. -/
def boundaryOrthogonalEquivExchangeKernel : K ≃ₗ[ℤ] E :=
  boundaryOrthogonalBasis.equivFun.trans exchangeKernelEquiv

/-- Each orthogonal basis vector gives the Casimir supported at the corresponding
pair of opposite vertices. -/
@[simp]
theorem boundaryOrthogonalEquivExchangeKernel_apply_basis (i : Fin 2) :
    boundaryOrthogonalEquivExchangeKernel (boundaryOrthogonalBasis i) =
      exchangeKernelEquiv (Pi.single i 1) := by
  rw [boundaryOrthogonalEquivExchangeKernel, LinearEquiv.trans_apply]
  apply congrArg exchangeKernelEquiv
  funext j
  simp only [Basis.equivFun_self, Pi.single_apply, eq_comm]

/-- The exchange-kernel basis matched to the two alternating Picard classes. -/
@[expose]
def exchangeKernelBasis : Basis (Fin 2) ℤ E :=
  boundaryOrthogonalBasis.map boundaryOrthogonalEquivExchangeKernel

/-- The basis is the image of the standard coordinate vectors under the exchange-kernel
equivalence. -/
@[simp]
theorem exchangeKernelBasis_apply (j : Fin 2) :
    exchangeKernelBasis j = exchangeKernelEquiv (Pi.single j 1) := by
  simp only [exchangeKernelBasis, Basis.map_apply,
    boundaryOrthogonalEquivExchangeKernel_apply_basis]

/-- The exponent at each vertex is the intersection with its internal exceptional
class, which is the negative of the coefficient of that class in the Picard marking. -/
theorem coe_boundaryOrthogonalEquivExchangeKernel_apply (x : K) :
    (boundaryOrthogonalEquivExchangeKernel x : Fin 4 → ℤ) =
      fun j ↦ intersectionForm x.val (Pi.single (j.natAdd 6) 1) := by
  let f : K →ₗ[ℤ] Fin 4 → ℤ :=
    LinearMap.pi fun j : Fin 4 ↦ (intersectionForm.flip (Pi.single (j.natAdd 6) 1)).comp (K).subtype
  have he : (E).subtype.comp boundaryOrthogonalEquivExchangeKernel.toLinearMap = f := by
    apply boundaryOrthogonalBasis.ext
    intro i
    funext j
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      boundaryOrthogonalEquivExchangeKernel_apply_basis, coe_exchangeKernelEquiv_apply, f,
      LinearMap.pi_apply, LinearMap.BilinForm.flip_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [intersectionForm_apply, Fin.sum_univ_succ, Pi.single_apply]
  funext j
  simpa only [f, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.pi_apply, LinearMap.BilinForm.flip_apply] using congrFun (LinearMap.congr_fun he x) j

/-- The total boundary class belongs to the Picard orthogonal lattice. -/
theorem sum_boundaryClass_mem_orthogonal : (∑ j, boundaryClass j) ∈ K := by
  rw [← sum_boundaryOrthogonalBasis, ← Submodule.coe_sum]
  exact (∑ i, boundaryOrthogonalBasis i).property

local notation "δ" => (Subtype.mk (∑ j, boundaryClass j) sum_boundaryClass_mem_orthogonal : K)

private theorem repr_sum_boundaryClass (i : Fin 2) :
    boundaryOrthogonalBasis.repr δ i = 1 := by
  have h : δ = ∑ j, boundaryOrthogonalBasis j := by
    apply Subtype.ext
    rw [Submodule.coe_sum, sum_boundaryOrthogonalBasis]
  rw [h]
  simpa only [one_smul, Pi.one_apply] using
    congrFun (boundaryOrthogonalBasis.repr_sum_self (1 : Fin 2 → ℤ)) i

/-- The total boundary is the null vector with affine coordinates `(1, 1)`. -/
@[simp]
theorem boundaryOrthogonalIsometryNegAffineA1_tmul_sum_boundaryClass :
    boundaryOrthogonalIsometryNegAffineA1 (1 ⊗ₜ[ℤ] δ) = 1 := by
  rw [boundaryOrthogonalIsometryNegAffineA1_apply_tmul]
  funext i
  simp only [repr_sum_boundaryClass, Int.cast_one, Pi.one_apply]

/-- The total boundary corresponds to the product of all four X coordinates. -/
@[simp]
theorem coe_boundaryOrthogonalEquivExchangeKernel_sum_boundaryClass :
    (boundaryOrthogonalEquivExchangeKernel δ : Fin 4 → ℤ) = 1 := by
  simp only [boundaryOrthogonalEquivExchangeKernel, LinearEquiv.trans_apply,
    coe_exchangeKernelEquiv_apply, Basis.equivFun_apply, repr_sum_boundaryClass]
  funext i
  fin_cases i <;> rfl

end QPainleve.FourVertex
