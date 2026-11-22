/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.IsotropicQuotient
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The isotropic lattice quotient in signature `(1, 9)`

The primitive characteristic isotropic class gives a rank-eight even unimodular
quotient with negative definite form.
-/

public section

open Submodule LinearMap

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] {B : LinearMap.BilinForm ℤ M} {δ : M}
variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For a primitive characteristic isotropic vector in a unimodular integral form of
signature `(1, 9)`, the quotient is a free rank-eight even unimodular lattice whose
scalar-extended form is negative definite. -/
theorem IsSymm.orthogonalQuotientForm_of_signature_one_nine (hB : B.IsSymm)
    [Module.Free ℤ M] [Module.Finite ℤ M] [B.IsPerfPair] (hδ : B δ δ = 0)
    (hprim : ∃ ℓ : M →ₗ[ℤ] ℤ, ℓ δ = 1) (hchar : B.IsCharacteristic δ)
    (hpos : sigPos (B.baseChange K).toQuadraticMap = 1)
    (hneg : sigNeg (B.baseChange K).toQuadraticMap = 9) :
    let F := B.orthogonalQuotientForm hB (ℤ ∙ δ)
    Module.Free ℤ (B.OrthogonalQuotient (ℤ ∙ δ)) ∧
      Module.finrank ℤ (B.OrthogonalQuotient (ℤ ∙ δ)) = 8 ∧
      F.IsPerfPair ∧ (∀ x, Even (F x x)) ∧ (-(F.baseChange K).toQuadraticMap).PosDef := by
  obtain ⟨ℓ, hℓ⟩ := hprim
  obtain ⟨f, rfl⟩ := (LinearMap.IsPerfPair.bijective_left B).surjective ℓ
  have hδf : B δ f = 1 := (hB.eq δ f).trans hℓ
  let e := hB.isometryEquivOrthogonalQuotient hδ hδf
  have hfree := Module.Free.of_equiv e.toLinearEquiv
  have hperf := hB.isPerfPair_orthogonalQuotientForm hδ hδf
  let F := B.orthogonalQuotientForm hB (ℤ ∙ δ)
  suffices Module.Free ℤ (B.OrthogonalQuotient (ℤ ∙ δ)) ∧
      Module.finrank ℤ (B.OrthogonalQuotient (ℤ ∙ δ)) = 8 ∧ F.IsPerfPair ∧
      (∀ x, Even (F x x)) ∧ (-(F.baseChange K).toQuadraticMap).PosDef from this
  have hnd : F.Nondegenerate := ⟨hperf.separatingLeft, hperf.separatingRight⟩
  have hndK := (F.nondegenerate_baseChange_iff (A := K) (Module.Free.chooseBasis ℤ _)).mpr hnd
  have hsymmK : (F.baseChange K).IsSymm := isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange K
      (isSymm_iff.mp (B.isSymm_orthogonalQuotientForm hB (ℤ ∙ δ))))
  have hreg := hndK.toQuadraticMap (LinearMap.ext₂ fun x y ↦ hsymmK.eq y x)
  obtain ⟨hp, hn⟩ := hB.sig_orthogonalQuotientForm K hδ hδf
  have hp' : sigPos (F.baseChange K).toQuadraticMap = 0 := by dsimp only [F]; omega
  have hn' : sigNeg (F.baseChange K).toQuadraticMap = 8 := by dsimp only [F]; omega
  have hsum := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate (F.baseChange K).toQuadraticMap hreg
  rw [Module.finrank_baseChange] at hsum
  refine ⟨hfree, by omega, hperf, hchar.even_orthogonalQuotientForm hB, ?_⟩
  rw [QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot, sigNeg_neg,
    QuadraticMap.radical_neg, hreg.radical_eq_bot]
  exact ⟨hp', rfl⟩

end LinearMap.BilinForm
