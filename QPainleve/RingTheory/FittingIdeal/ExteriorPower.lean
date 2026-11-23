/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.RingTheory.FittingIdeal.Determinant

/-!
# Fitting ideals of top exterior power maps

For a linear map between free modules of the same finite rank, the zeroth Fitting
ideal of the cokernel agrees with that of the top exterior power map over any
commutative ring. This uses Tau Ceti's square-presentation formula and its
computation of the action of an endomorphism on the top exterior power.

See the Stacks Project, Sections 15.8 (tag 07Z6) and 15.120 (tag 0FJ9).
-/

public section

namespace LinearMap

open Module

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- Taking the top exterior power of a map between finite free modules of the same rank
preserves the zeroth Fitting ideal of its cokernel. -/
theorem fittingIdeal_coker_zero_exteriorPower (f : M →ₗ[R] N) {n : ℕ}
    (hM : finrank R M = n) (hN : finrank R N = n) :
    TauCeti.fittingIdeal R (⋀[R]^n N ⧸ range (exteriorPower.map n f)) 0 =
      TauCeti.fittingIdeal R (N ⧸ range f) 0 := by
  nontriviality R
  let b := Module.finBasisOfFinrankEq R N hN
  let e := (Module.finBasisOfFinrankEq R M hM).equiv b (Equiv.refl _)
  let g := f.comp e.symm.toLinearMap
  have hrange : range g = range f :=
    range_comp_of_range_eq_top f (range_eq_top.mpr e.symm.surjective)
  have hwedge : range (exteriorPower.map n g) = range (exteriorPower.map n f) := by
    dsimp only [g]
    rw [exteriorPower.map_comp]
    exact range_comp_of_range_eq_top _ (range_eq_top.mpr
      (exteriorPower.map_surjective e.symm.surjective))
  let w := b.exteriorPowerTopEquiv
  let := Module.Free.of_equiv w.symm
  have hdim : finrank R (⋀[R]^n N) = 1 := w.finrank_eq.trans (Module.finrank_self R)
  rw [← hwedge, ← hrange, fittingIdeal_coker_zero_eq_span_det,
    fittingIdeal_coker_zero_eq_span_det, b.map_exteriorPower_top_eq_det_smul,
    LinearMap.det_smul, LinearMap.det_id, hdim, pow_one, mul_one]

end LinearMap
