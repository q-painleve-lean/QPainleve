/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Orders at closed points

At a closed point, a lower bound on the order of an ideal is equivalent to containment
in the corresponding power of the reduced point ideal. On each affine neighborhood,
Mathlib's contraction theorem for powers of a maximal ideal compares the two conditions.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (p : X)

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)

/-- At a closed point, the stalk order bound can be checked by containment in the
corresponding maximal-ideal power on any affine neighborhood. -/
theorem natCast_le_stalkOrder_iff_ideal_le_pow (J : X.IdealSheafData)
    (hp : IsClosed ({p} : Set X)) (U : X.affineOpens) (hpU : p ∈ U.val) (n : ℕ) :
    (n : ℕ∞) ≤ J.stalkOrder p ↔ J.ideal U ≤ ((Iₚ).ideal U) ^ n := by
  let q := U.property.primeIdealOf ⟨p, hpU⟩
  have : q.asIdeal.IsMaximal := U.property.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  have hq : Ideal.comap (algebraMap Γ(X, U) (Localization.AtPrime q.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ n) = q.asIdeal ^ n :=
    IsLocalization.AtPrime.under_maximalIdeal_pow q.asIdeal _ n
  rw [J.stalkOrder_eq_orderAt U p hpU, Ideal.natCast_le_orderAt_iff,
    Ideal.map_le_iff_le_comap, hq,
    X.ker_fromSpecResidueField_eq_vanishingIdeal, vanishingIdeal_closure_singleton_ideal p U hpU]

/-- The order at a closed point is at least `n` exactly when the ideal sheaf is
contained in the `n`-th power of the reduced point ideal. -/
theorem natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField (J : X.IdealSheafData)
    (hp : IsClosed ({p} : Set X)) (n : ℕ) :
    (n : ℕ∞) ≤ J.stalkOrder p ↔ J ≤ Iₚ ^ n := by
  constructor
  · intro h U
    rw [ideal_pow, Pi.pow_apply]
    by_cases hpU : p ∈ U.val
    · exact (natCast_le_stalkOrder_iff_ideal_le_pow p J hp U hpU n).mp h
    · have hU : IsAffineOpen U.val := U.property
      have hpre : (fun y : PrimeSpectrum Γ(X, U) ↦ hU.fromSpec y) ⁻¹'
          closure ({p} : Set X) = ∅ := by
        rw [hp.closure_eq, Set.eq_empty_iff_forall_notMem]
        intro y hy
        have hpy : hU.fromSpec y = p := Set.mem_singleton_iff.mp hy
        have hyU : hU.fromSpec y ∈ (U.val : Set X) := hU.range_fromSpec ▸ Set.mem_range_self y
        exact hpU (hpy ▸ hyU)
      rw [X.ker_fromSpecResidueField_eq_vanishingIdeal, vanishingIdeal_ideal,
        Closeds.coe_mk]
      -- The affine chart in the vanishing-ideal formula uses its stored affine-open proof.
      erw [hpre]
      rw [PrimeSpectrum.vanishingIdeal_empty, Ideal.top_pow]
      exact le_top
  · intro h
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top p)
    exact (natCast_le_stalkOrder_iff_ideal_le_pow p J hp ⟨U, hU⟩ hpU n).mpr
      (by simpa only [ideal_pow, Pi.pow_apply] using h ⟨U, hU⟩)

end AlgebraicGeometry.Scheme.IdealSheafData
