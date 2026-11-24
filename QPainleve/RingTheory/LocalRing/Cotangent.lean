/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of the cotangent space of a local algebra

The residue field and the cotangent space account for the dimension of the
square-zero truncation of a local algebra. When the coefficient field is the
residue field, the cotangent dimension counts generators of the maximal ideal.
-/

public section

namespace IsLocalRing

variable (k R : Type*) [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]

private theorem exact_cotangentToQuotientSquare_factor :
    Function.Exact
      ((maximalIdeal R).cotangentToQuotientSquare.restrictScalars k)
      (Ideal.Quotient.factorₐ k
        (Ideal.pow_le_self (I := maximalIdeal R) two_ne_zero)).toLinearMap := by
  rw [LinearMap.exact_iff]
  ext a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  -- Evaluate the quotient factor and the kernel condition on a representative.
  change Ideal.Quotient.mk (maximalIdeal R) r = 0 ↔
    Ideal.Quotient.mk (maximalIdeal R ^ 2) r ∈
      LinearMap.range ((maximalIdeal R).cotangentToQuotientSquare.restrictScalars k)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    exact ⟨(maximalIdeal R).toCotangent ⟨r, hr⟩,
      (maximalIdeal R).toCotangent_to_quotient_square ⟨r, hr⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective t
    rw [LinearMap.restrictScalars_apply, Ideal.toCotangent_to_quotient_square] at ht
    exact (Ideal.mk_mem_cotangentIdeal.mp (ht ▸ Ideal.mk_mem_cotangentIdeal.mpr x.property))

/-- The quotient by the squared maximal ideal of a Noetherian local algebra is
finite over the base field when its residue field is finite over the base field. -/
theorem finite_quotient_maximalIdeal_sq [IsNoetherianRing R] [Module.Finite k (ResidueField R)] :
    Module.Finite k (R ⧸ maximalIdeal R ^ 2) := by
  let : IsScalarTower k (ResidueField R) (CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun c x ↦ by
      rw [IsScalarTower.algebraMap_apply k R (ResidueField R), algebraMap_smul, algebraMap_smul]
  let : Module.Finite k (CotangentSpace R) := FiniteDimensional.trans k (ResidueField R) _
  let : Module.Finite k (R ⧸ maximalIdeal R) :=
    inferInstanceAs (Module.Finite k (ResidueField R))
  exact Module.Finite.of_exact (exact_cotangentToQuotientSquare_factor k R)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero))

/-- The dimension of the quotient by the squared maximal ideal is the sum of the
cotangent dimension and the residue field dimension, measured over the coefficient field. -/
theorem finrank_quotient_maximalIdeal_sq [Module.Finite k (R ⧸ maximalIdeal R ^ 2)] :
    Module.finrank k (R ⧸ maximalIdeal R ^ 2) =
      Module.finrank k (CotangentSpace R) + Module.finrank k (ResidueField R) := by
  let m := maximalIdeal R
  have hle : m ^ 2 ≤ m := Ideal.pow_le_self two_ne_zero
  let q := Ideal.Quotient.factorₐ k hle
  let j := m.cotangentToQuotientSquare.restrictScalars k
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hle
  have hj : Function.Injective j := m.cotangentToQuotientSquare_injective
  have hker : LinearMap.ker q.toLinearMap = LinearMap.range j :=
    (exact_cotangentToQuotientSquare_factor k R).linearMap_ker_eq
  have h := q.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, hker, LinearMap.finrank_range_of_inj hj] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- For a coefficient field that maps onto the residue field, the cotangent dimension
over the coefficient field is the minimum number of generators of the maximal ideal. -/
theorem spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_residue_surjective
    (hfg : (maximalIdeal R).FG) (h : Function.Surjective (algebraMap k (ResidueField R))) :
    (maximalIdeal R).spanFinrank = Module.finrank k (CotangentSpace R) := by
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg]
  have hr := Module.finrank_of_bijective_algebraMap
    ⟨(algebraMap k (ResidueField R)).injective, h⟩
  let : IsScalarTower k (ResidueField R) (CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun c x ↦ by
      rw [IsScalarTower.algebraMap_apply k R (ResidueField R), algebraMap_smul, algebraMap_smul]
  have hd := Module.finrank_mul_finrank k (ResidueField R) (CotangentSpace R)
  rwa [hr, one_mul] at hd

end IsLocalRing
