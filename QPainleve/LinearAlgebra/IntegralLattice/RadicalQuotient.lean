/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RadicalQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Radical quotients of integral bilinear forms

For a symmetric form on a finite free integer module, the rational radical is the scalar
extension of the integral kernel. Quotienting by that kernel recovers the integral form of
Tau Ceti's `IntegralLattice.radicalQuotient`. The comparison uses its
`ofIntegralForm.carrierEquiv` and Mathlib's `LinearMap.quotKerEquivOfSurjective`.
-/

public section

open LinearMap Submodule TensorProduct

namespace TauCeti.IntegralLattice.ofIntegralForm

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
  {B : LinearMap.BilinForm ℤ M} (hB : B.IsSymm)

/-- The quotient of the rationalized lattice kills an integral vector exactly when it is
in the kernel of the original form. -/
theorem radicalQuotientMap_carrierEquiv_eq_zero_iff (x : M) :
    (ofIntegralForm B hB).radicalQuotientMap (carrierEquiv B hB x) = 0 ↔ x ∈ B.ker := by
  rw [radicalQuotientMap_eq_zero_iff, coe_carrierEquiv_apply, mem_radical_iff, ofIntegralForm_form]
  constructor
  · intro hx
    refine mem_ker.mpr (LinearMap.ext fun y ↦ Int.cast_injective (α := ℚ) ?_)
    simpa using hx (1 ⊗ₜ[ℤ] y)
  · intro hx
    have h : B.baseChange ℚ (1 ⊗ₜ[ℤ] x) = 0 := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a y
      simp [mem_ker.mp hx]
    simp [h]

/-- The rational radical of a rationalized integral form is the scalar extension of
its integral kernel. -/
theorem radical_eq_baseChange_ker :
    (ofIntegralForm B hB).radical = B.ker.baseChange ℚ := by
  let e := TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := ℤ) (A := ℚ) (M := M)
  have h : B.baseChange ℚ = e.toLinearMap.comp (LinearMap.baseChange ℚ B) := by
    ext x y
    simp [e, LinearMap.baseChange_tmul, TauCeti.Module.Dual.baseChangeEvaluation_tmul]
  have hker : (B.baseChange ℚ).ker = B.ker.baseChange ℚ := by
    rw [h, ker_comp_of_ker_eq_bot _ e.ker, ker_baseChange_of_flat]
  rw [← hker]
  ext z
  simp [mem_ker, LinearMap.ext_iff, ofIntegralForm_form]

/-- The quotient form by the integral kernel agrees with the integral form of the native
radical quotient. The denominator may be given by an explicit submodule equal to the kernel. -/
noncomputable def radicalQuotientIsometry (P : Submodule ℤ M) (hP : P = B.ker) :
    LinearMap.BilinForm.IsometryEquiv (hB.isRefl.liftQ₂ B P hP.le)
      (ofIntegralForm B hB).radicalQuotient.integralForm := by
  let L := ofIntegralForm B hB
  let f := L.radicalQuotientMap.comp (carrierEquiv B hB).toLinearMap
  have hf : f.ker = B.ker := by
    ext x
    exact radicalQuotientMap_carrierEquiv_eq_zero_iff hB x
  let e := (Submodule.quotEquivOfEq P f.ker (hP.trans hf.symm)).trans
      (f.quotKerEquivOfSurjective
        (L.radicalQuotientMap_surjective.comp (carrierEquiv B hB).surjective))
  refine ⟨e, fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := P.mkQ_surjective x
  obtain ⟨y, rfl⟩ := P.mkQ_surjective y
  simp [e, f, L]

/-- The comparison sends an integral quotient class to the native class of its unit tensor. -/
@[simp]
theorem radicalQuotientIsometry_mk (P : Submodule ℤ M) (hP : P = B.ker) (x : M) :
    radicalQuotientIsometry hB P hP (Submodule.Quotient.mk x) =
      (ofIntegralForm B hB).radicalQuotientMap (carrierEquiv B hB x) := by
  rw [← BilinForm.IsometryEquiv.coe_toLinearEquiv]
  simp [radicalQuotientIsometry]

end TauCeti.IntegralLattice.ofIntegralForm
