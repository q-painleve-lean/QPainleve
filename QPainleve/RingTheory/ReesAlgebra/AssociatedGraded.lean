/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import QPainleve.RingTheory.Ideal.AssociatedGraded
public import TauCeti.RingTheory.ReesAlgebra.AssociatedGraded

import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Graded base change of the Rees algebra to the center

The Rees symbol map is graded, and identifies the associated graded ring as the base change
of the Rees algebra along the quotient by the center ideal. The comparison uses Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and Tau Ceti's
`Ideal.ReesQuotient.equivAssociatedGraded`.
-/

public section

namespace reesAlgebra

open scoped TensorProduct

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The Rees symbol map as a degree-preserving ring homomorphism. -/
noncomputable def gradedToAssociatedGraded :
    grade I →+*ᵍ Ideal.AssociatedGraded.grade I where
  toRingHom := (toAssociatedGraded I).toRingHom
  map_mem {n} x hx := by
    obtain ⟨r, hr, heq⟩ := mem_grade_iff.mp hx
    have h : x = ⟨Polynomial.monomial n r, monomial_mem.mpr hr⟩ := Subtype.ext heq.symm
    rw [h, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, toAssociatedGraded_monomial hr,
      Ideal.AssociatedGraded.mk_apply]
    exact Ideal.AssociatedGraded.of_mem_grade I _ _

/-- The graded Rees symbol map has the same values as the underlying algebra map. -/
@[simp]
theorem gradedToAssociatedGraded_apply (x : reesAlgebra I) :
    gradedToAssociatedGraded I x = toAssociatedGraded I x :=
  (rfl)

/-- The degree-one Rees monomial of a center element maps to its class in degree one. -/
@[simp]
theorem toAssociatedGraded_monomialDegreeOne {a : R} (ha : a ∈ I) :
    toAssociatedGraded I (monomialDegreeOne ha) =
      Ideal.AssociatedGraded.mk I 1 ⟨a, by simpa only [pow_one] using ha⟩ := by
  have ha' : a ∈ I ^ 1 := by simpa only [pow_one] using ha
  have h : monomialDegreeOne ha = ⟨Polynomial.monomial 1 a, monomial_mem.mpr ha'⟩ :=
    Subtype.ext (coe_monomialDegreeOne ha)
  rw [h, toAssociatedGraded_monomial ha']

/-- The graded Rees symbol map is surjective. -/
theorem gradedToAssociatedGraded_surjective :
    Function.Surjective (gradedToAssociatedGraded I) := by
  simpa only [Function.Surjective, gradedToAssociatedGraded_apply] using
    toAssociatedGraded_surjective I

/-- The symbol map realizes the associated graded ring as the base change of the Rees ring
to the quotient by the center ideal. -/
theorem isBaseChange_toAssociatedGraded :
    IsBaseChange (R ⧸ I) (toAssociatedGraded I).toLinearMap := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (reesAlgebra I) I
  refine IsBaseChange.of_equiv
    (e.symm.trans (Ideal.ReesQuotient.equivAssociatedGraded I)).toLinearEquiv ?_
  intro x
  have hx : e (Ideal.Quotient.mk _ x) = 1 ⊗ₜ[R] x :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk _ _ x
  simp only [AlgEquiv.toLinearEquiv_apply, AlgEquiv.trans_apply, ← hx,
    AlgEquiv.symm_apply_apply, Ideal.ReesQuotient.equivAssociatedGraded_quotientMk,
    AlgHom.toLinearMap_apply]

end reesAlgebra
