/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.Topology.KrullDimension.Basic

/-!
# Local dimension along an effective Cartier divisor

The local ring of an effective Cartier divisor has dimension one less than the ambient local
ring. The comparison uses the closed-immersion stalk map and the nonzerodivisor equation of the
divisor. The dimension formula for the quotient is
[The Stacks Project, Lemma 10.60.13](https://stacks.math.columbia.edu/tag/00KW).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme} [IsLocallyNoetherian X] {I : X.IdealSheafData}

/-- At a point of an effective Cartier divisor, the dimension of its local ring plus one is
the dimension of the ambient local ring. -/
theorem IsEffectiveCartier.ringKrullDim_stalk_add_one (hI : I.IsEffectiveCartier)
    (x : I.subscheme) :
    ringKrullDim (I.subscheme.presheaf.stalk x) + 1 =
      ringKrullDim (X.presheaf.stalk (I.subschemeι x)) := by
  let y := I.subschemeι x
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  obtain ⟨a, ha, hspan⟩ := hI.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hyU
  let f := (I.subschemeι.stalkMap x).hom
  have hf : Function.Surjective f := I.subschemeι.stalkMap_surjective x
  have hk : RingHom.ker f = Ideal.span {a} := by
    rw [Scheme.Hom.ker_stalkMap_of_isClosedImmersion, ker_subschemeι,
      I.stalkIdeal_eq_map ⟨U, hU⟩ y hyU, hspan]
  have hamem : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f))
      (hk ▸ Ideal.mem_span_singleton_self a)
  let e := (Ideal.quotEquivOfEq hk.symm).trans (f.quotientKerEquivOfSurjective hf)
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim ha hamem

/-- An effective Cartier divisor in a scheme of dimension at most `d + 1`
has dimension at most `d`. This includes the empty divisor. -/
theorem IsEffectiveCartier.topologicalKrullDim_subscheme_le (hI : I.IsEffectiveCartier)
    {d : ℕ} (hX : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim I.subscheme ≤ d := by
  rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  rw [← ringKrullDim_stalk_eq_coheight]
  apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
  rw [Nat.cast_one, hI.ringKrullDim_stalk_add_one, ringKrullDim_stalk_eq_coheight]
  exact (TauCeti.coheight_le_topologicalKrullDim (I.subschemeι x)).trans
    (by simpa only [Nat.cast_add, Nat.cast_one] using hX)

end AlgebraicGeometry.Scheme.IdealSheafData
