/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Word
public import QPainleve.Algebra.Cluster.XMutation.Monomial

/-!
# Cluster mutation of charge monomials

The Laurent monomial of a charge relation pulls back to the monomial of the transported
relation. The binomial factor in the X formula of Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.4, cancels on the charge kernel.
-/

public noncomputable section

open scoped Int

namespace QPainleve.Cluster

open CharacterTorus

variable (k : Type*) [Field k] {ι : Type*} [Fintype ι]
variable [DecidableEq ι] {N : Type*} [AddCommGroup N] {B : SkewExchangeMatrix ι}

/-- Pulling a monomial from the mutated charge kernel back to the original torus
uses the same exponent substitution as the integral change of basis. -/
theorem xMutation_apply_chargeMonomial (P : ChargeSeed B N) (j : ι)
    (x : (Step.chargeTarget ((Generator.mutate j).toStep B) P).charge.ker) :
    xMutation k j (fun i ↦ B.matrix i j)
      (monomial k (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (x : ι → ℤ)))) =
    monomial k (Multiplicative.ofAdd
      (Finsupp.equivFunOnFinite.symm (Step.exponentEquiv ((Generator.mutate j).toStep B)
        (x : ι → ℤ)))) := by
  have hx : (x : ι → ℤ) ∈ (chargeMutation P.form P.charge j).ker := by
    simpa only [Step.chargeTarget_mutate_charge] using x.property
  have h := prod_zpow_xMutation_eq P.form P.isAlt P.charge j ⟨x, hx⟩ (xCoordinate k)
    (xCoordinate_ne_zero k j) (one_add_xCoordinate_ne_zero k j)
  simp only [monomial_eq_prod_zpow_xCoordinate, map_prod, map_zpow₀, Step.exponentEquiv_mutate]
  rw [← P.matrix_eq]
  simp only [coe_chargeKernelMutation_apply] at h
  refine .trans (Finset.prod_congr rfl fun i _ ↦ ?_) h
  by_cases hi : i = j
  · subst i
    simp
  · simp [hi, xMutation_apply_of_ne, posPart_def]

end QPainleve.Cluster
