/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# Monomial valuations on monoid algebra fraction fields

A weight homomorphism gives a valuation by taking the minimum weight in the
support of a monoid algebra element. Distinct monomials of a common weight
remain independent in the coefficient field of the Hahn-series realization.
-/

public noncomputable section

namespace AddMonoidAlgebra

variable {k M Γ : Type*} [CommRing k] [AddCommMonoid M]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

local notation "R" => AddMonoidAlgebra k M
local notation "K" => FractionRing R
local notation "inK" => algebraMap R K

private def weightedSeries (w : M →+ Γ) : R →ₐ[k] HahnSeries Γ K :=
  AddMonoidAlgebra.lift k _ M
    { toFun := fun a => HahnSeries.single (w a.toAdd) (inK (single a.toAdd 1))
      map_one' := by simp [← one_def]
      map_mul' := fun a b => by simp [HahnSeries.single_mul_single, ← map_mul, single_mul_single] }

private theorem weightedSeries_single (w : M →+ Γ) (a : M) (c : k) :
    weightedSeries w (single a c) = HahnSeries.single (w a) (inK (single a c)) := by
  rw [weightedSeries, lift_single]
  apply HahnSeries.ext
  funext g
  by_cases h : g = w a
  · subst g
    have hs : c • inK (single a 1) = inK (c • single a 1) :=
      ((IsScalarTower.toAlgHom k R K).toLinearMap.map_smul c (single a 1)).symm
    simpa [HahnSeries.coeff_smul, smul_single] using hs
  · simp [HahnSeries.coeff_smul, HahnSeries.coeff_single_of_ne h]

private theorem weightedSeries_coeff (w : M →+ Γ) (p : R) (g : Γ) :
    (weightedSeries w p).coeff g =
      inK (∑ a ∈ p.coeff.support with w a = g, single a (p.coeff a)) := by
  classical
  calc
    (weightedSeries w p).coeff g =
        (weightedSeries w (p.coeff.sum single)).coeff g := by rw [sum_coeff_single]
    _ = _ := by
      simp [Finsupp.sum, weightedSeries_single, HahnSeries.coeff_sum, HahnSeries.coeff_single,
        Finset.sum_filter, eq_comm (a := g), apply_ite]

private theorem weightedSeries_coeff_ne_zero_iff (w : M →+ Γ) (p : R) (g : Γ) :
    (weightedSeries w p).coeff g ≠ 0 ↔ ∃ a ∈ p.coeff.support, w a = g := by
  classical
  rw [weightedSeries_coeff, map_ne_zero_iff _ (IsFractionRing.injective R K)]
  constructor
  · contrapose!
    intro h
    exact Finset.sum_eq_zero fun a ha => (h a (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp ha).2).elim
  · rintro ⟨a, ha, hw⟩ h
    have hcoeff := congrArg (fun q : R => q.coeff a) h
    rw [coeff_sum, Finset.sum_apply', Finset.sum_eq_single a] at hcoeff
    · exact Finsupp.mem_support_iff.mp ha (by simpa [coeff_single] using hcoeff)
    · intro b _ hba
      exact Finsupp.single_eq_of_ne hba.symm
    · exact fun hnot => (hnot (Finset.mem_filter.mpr ⟨ha, hw⟩)).elim

private theorem weightedSeries_injective (w : M →+ Γ) :
    Function.Injective (weightedSeries (k := k) w) := by
  apply (injective_iff_map_eq_zero _).2
  intro p hp
  apply coeff_injective
  ext a
  by_contra ha
  have := (weightedSeries_coeff_ne_zero_iff w p (w a)).2
    ⟨a, Finsupp.mem_support_iff.mpr (by simpa using ha), rfl⟩
  exact this (by rw [hp]; simp)

variable [IsDomain (AddMonoidAlgebra k M)]

/-- The valuation that assigns weight `w a` to exponent `a` and takes the minimum
over the nonzero terms of a monoid algebra element. -/
def monomialAddValuation (w : M →+ Γ) : AddValuation K (WithTop Γ) :=
  (HahnSeries.addVal Γ K).comap
    (IsFractionRing.lift (g := (weightedSeries (k := k) w).toRingHom) (weightedSeries_injective w))

/-- On the monoid algebra the valuation is the minimum weight in the support,
with value `⊤` for the empty support. -/
theorem monomialAddValuation_algebraMap (w : M →+ Γ) (p : R) :
    monomialAddValuation (k := k) w (inK p) = p.coeff.support.inf fun a => (w a : WithTop Γ) := by
  -- The valuation is pulled back through the extension of the Hahn-series map.
  change HahnSeries.addVal Γ K
    (IsFractionRing.lift (g := (weightedSeries (k := k) w).toRingHom)
      (weightedSeries_injective w) (inK p)) = _
  rw [IsFractionRing.lift_algebraMap, HahnSeries.addVal_apply]
  apply eq_of_forall_le_iff
  intro t
  rw [HahnSeries.le_orderTop_iff_forall, Finset.le_inf_iff]
  constructor
  · intro h a ha
    exact le_of_not_gt fun ht => (weightedSeries_coeff_ne_zero_iff w p (w a)).mpr
      ⟨a, ha, rfl⟩ (h _ ht)
  · intro h g hg
    by_contra hne
    obtain ⟨a, ha, rfl⟩ := (weightedSeries_coeff_ne_zero_iff w p g).mp hne
    exact (not_lt_of_ge (h a ha)) hg

/-- The value of a nonzero monomial is the weight of its exponent. -/
@[simp]
theorem monomialAddValuation_single (w : M →+ Γ) (a : M) {c : k} (hc : c ≠ 0) :
    monomialAddValuation (k := k) w (inK (single a c)) = w a := by
  classical
  simp [monomialAddValuation_algebraMap, coeff_single, Finsupp.support_single a hc]

/-- Relabeling the exponent monoid transports the valuation by precomposing
the weight with the exponent equivalence. -/
theorem monomialAddValuation_domCongr {M' : Type*} [AddCommMonoid M']
    [IsDomain (AddMonoidAlgebra k M')] (w : M →+ Γ) (e : M' ≃+ M)
    (f : FractionRing (AddMonoidAlgebra k M')) :
    monomialAddValuation (k := k) w (IsFractionRing.algEquivOfAlgEquiv (domCongr k k e) f) =
      monomialAddValuation (k := k) (w.comp e.toAddMonoidHom) f := by
  have hmap (p : AddMonoidAlgebra k M') :
      monomialAddValuation (k := k) w (inK (domCongr k k e p)) =
        monomialAddValuation (k := k) (w.comp e.toAddMonoidHom)
          (algebraMap (AddMonoidAlgebra k M') _ p) := by
    rw [monomialAddValuation_algebraMap, monomialAddValuation_algebraMap,
      domCongr_support, Finset.inf_map]
    rfl
  obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (AddMonoidAlgebra k M')) f
  simp [IsFractionRing.mk'_eq_div, IsFractionRing.algEquivOfAlgEquiv_algebraMap, hmap]

end AddMonoidAlgebra
