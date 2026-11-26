/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes

/-!
# Boundary primes of an effective Cartier divisor

The codimension-one points of the support of an effective Cartier divisor index
the nonzero coefficients of its Weil divisor.
-/

public section

open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme} [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}

/-- The boundary primes of an effective Cartier divisor are the support of its Weil divisor,
with each prime sent to the same codimension-one point. -/
noncomputable def boundaryPrimesEquivWeilSupport (hD : D.IsEffectiveCartier) :
    D.boundaryPrimes ≃ hD.toCartierDivisor.toWeilDivisor.support where
  toFun p := ⟨D.boundaryPrimeEmbedding p, WeilDivisor.mem_support_iff.mpr fun h ↦
    (hD.coeff_toWeilDivisor_eq_zero_iff _).mp h
      (by simpa only [coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp p.property).1)⟩
  invFun p := ⟨p.val, mem_boundaryPrimes.mpr
    ⟨by
      by_contra h
      exact (WeilDivisor.mem_support_iff.mp p.property)
        ((hD.coeff_toWeilDivisor_eq_zero_iff _).mpr h), p.val.property⟩⟩
  left_inv p := Subtype.ext (coe_boundaryPrimeEmbedding D p)
  right_inv p := Subtype.ext (Subtype.ext (coe_boundaryPrimeEmbedding D _))

/-- The Weil support point is the image of the boundary prime in codimension one. -/
@[simp]
theorem boundaryPrimesEquivWeilSupport_apply_val (hD : D.IsEffectiveCartier)
    (p : D.boundaryPrimes) :
    (hD.boundaryPrimesEquivWeilSupport p).val = D.boundaryPrimeEmbedding p :=
  (rfl)

/-- The inverse correspondence takes the underlying point of the Weil support prime. -/
@[simp]
theorem boundaryPrimesEquivWeilSupport_symm_apply_val (hD : D.IsEffectiveCartier)
    (p : hD.toCartierDivisor.toWeilDivisor.support) :
    (hD.boundaryPrimesEquivWeilSupport.symm p).val = (p.val : X) :=
  (rfl)

/-- The Weil multiplicity of an effective Cartier divisor at one of its boundary primes. -/
noncomputable def boundaryCoeff (hD : D.IsEffectiveCartier) (p : D.boundaryPrimes) : ℤ :=
  hD.toCartierDivisor.toWeilDivisor (D.boundaryPrimeEmbedding p)

/-- Boundary coefficients are evaluated at the corresponding codimension-one points. -/
theorem boundaryCoeff_def (hD : D.IsEffectiveCartier) (p : D.boundaryPrimes) :
    hD.boundaryCoeff p = hD.toCartierDivisor.toWeilDivisor (D.boundaryPrimeEmbedding p) :=
  (rfl)

/-- On a normal scheme, each boundary prime of an effective Cartier divisor has
strictly positive coefficient. -/
theorem boundaryCoeff_pos [IsNormalScheme X] (hD : D.IsEffectiveCartier) (p : D.boundaryPrimes) :
    0 < hD.boundaryCoeff p := by
  have hnonneg := (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
    hD.isEffective_toCartierDivisor
  rw [boundaryCoeff_def, ← hD.boundaryPrimesEquivWeilSupport_apply_val p]
  exact (hnonneg _).lt_of_ne (WeilDivisor.mem_support_iff.mp
    (hD.boundaryPrimesEquivWeilSupport p).property).symm

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
