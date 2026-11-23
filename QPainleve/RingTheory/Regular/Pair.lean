/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.RingTheory.Regular.Pair

/-!
# Permuting a weakly regular pair in a domain

A weakly regular generating pair of a proper ideal in a domain remains weakly
regular in the opposite order. This applies to either standard chart of a blowup,
including on an affine open where the center is a proper ideal.
-/

public section

namespace RingTheory.Sequence.IsWeaklyRegular

variable {R : Type*} [CommRing R] [IsDomain R] {a b : R}

/-- A weakly regular pair in a domain generating a proper ideal can be swapped. -/
theorem swap_of_span_ne_top (h : IsWeaklyRegular R [a, b])
    (hproper : Ideal.span {a, b} ≠ ⊤) : IsWeaklyRegular R [b, a] := by
  have hb : b ≠ 0 := by
    intro hb
    have hmod := ((isWeaklyRegular_cons_iff R a [b]).mp h).2
    rw [isWeaklyRegular_singleton_iff, TauCeti.isSMulRegular_quotSMulTop_iff] at hmod
    have ha := hmod 1 0 (by simp [hb])
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top] at ha
    exact hproper ((Ideal.eq_top_iff_one _).mpr
      (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert a {b})) ha))
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨IsSMulRegular.of_ne_zero hb, ?_⟩
  have hr : IsSMulRegular (QuotSMulTop (b ^ 1) R) a := by
    simpa only [pow_one] using h.isSMulRegular_quotSMulTop_pow_swap 1 1
  exact pow_one b ▸ hr

end RingTheory.Sequence.IsWeaklyRegular
