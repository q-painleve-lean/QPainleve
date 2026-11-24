/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Dimensions of truncations in total degree

Quotienting a multivariate polynomial or power series ring by the `(n + 1)`st
power of the variable ideal leaves the monomials of total degree at most `n`.
For power series, the comparison uses Mathlib's `MvPowerSeries.toAdicCompletionAlgEquiv`.
-/

public section

namespace MvPolynomial

variable (σ k : Type*) [Fintype σ] [CommRing k] [StrongRankCondition k]

/-- The quotient by the `(n + 1)`st power of the variable ideal has the dimension
of the polynomials of total degree at most `n`. -/
theorem finrank_quotient_idealOfVars_pow (n : ℕ) :
    Module.finrank k (MvPolynomial σ k ⧸ idealOfVars _ k ^ (n + 1)) =
      (n + Fintype.card σ).choose (Fintype.card σ) := by
  let J := idealOfVars σ k ^ (n + 1)
  let S := restrictTotalDegree σ k n
  let q := (Ideal.Quotient.mkₐ k J).toLinearMap.comp S.subtype
  have hq : Function.Bijective q := by
    refine ⟨(injective_iff_map_eq_zero q).mpr ?_, ?_⟩
    · intro p hp
      have hp' : (p : MvPolynomial σ k) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hp
      ext m
      by_cases hm : m.degree < n + 1
      · simpa using (mem_pow_idealOfVars_iff' ..).mp hp' m hm
      · have hdeg := (mem_restrictTotalDegree _ _ _).mp p.property
        simpa using (notMem_support_iff.mp fun hs ↦ hm ((le_totalDegree hs).trans_lt
          (Nat.lt_succ_of_le hdeg)))
    · intro a
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      let t := MvPowerSeries.truncTotal (n + 1) (p : MvPowerSeries σ k)
      have ht : t ∈ S := (mem_restrictTotalDegree _ _ _).mpr
        (Nat.le_of_lt_succ (MvPowerSeries.totalDegree_truncTotal_lt _ (Nat.succ_ne_zero n)))
      refine ⟨⟨t, ht⟩, Ideal.Quotient.eq.mpr ?_⟩
      rw [mem_pow_idealOfVars_iff']
      intro m hm
      simp only [Submodule.coe_subtype, AddMonoidAlgebra.coeff_sub_apply, t,
        MvPowerSeries.coeff_truncTotal _ hm, coeff_coe, sub_self]
  exact (LinearEquiv.ofBijective q hq).finrank_eq.symm.trans
    (TauCeti.finrank_restrictTotalDegree σ k n)

end MvPolynomial

namespace MvPowerSeries

/-- The dimension of the quotient of a formal power series ring by the `(n + 1)`st
power of the variable ideal is the number of monomials of degree at most `n`. -/
theorem finrank_quotient_span_range_X_pow (σ k : Type*) [Fintype σ] [CommRing k]
    [StrongRankCondition k] (n : ℕ) :
    Module.finrank k (MvPowerSeries σ k ⧸
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (n + 1)) =
      (n + Fintype.card σ).choose (Fintype.card σ) := by
  let I := MvPolynomial.idealOfVars σ k
  let e := MvPowerSeries.toAdicCompletionAlgEquiv σ k
  have hmap : (Ideal.span (Set.range MvPowerSeries.X)).map e.toRingHom =
      I.map (algebraMap _ (AdicCompletion I (MvPolynomial σ k))) := by
    simp_rw [I, MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      MvPowerSeries.toAdicCompletion_coe]
  let J : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range MvPowerSeries.X)
  have hpows : (I ^ (n + 1)).map (algebraMap _ (AdicCompletion I (MvPolynomial σ k))) =
      (J ^ (n + 1)).map e.toRingHom := by
    simpa only [Ideal.map_pow] using congrArg (· ^ (n + 1)) hmap.symm
  let e₁ := Ideal.quotientEquivAlg _ _ (e.restrictScalars k) hpows
  let e₂ := (AdicCompletion.quotientMapPowAlgEquiv (MvPolynomial.fg_idealOfVars σ k)
    (n + 1)).restrictScalars k
  exact (e₁.trans e₂).toLinearEquiv.finrank_eq.trans
    (MvPolynomial.finrank_quotient_idealOfVars_pow σ k n)

end MvPowerSeries
