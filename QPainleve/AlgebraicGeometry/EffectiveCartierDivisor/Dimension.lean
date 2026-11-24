/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.Topology.KrullDimension.Basic
import TauCeti.Topology.Sober

/-!
# Local dimension along an effective Cartier divisor

The local ring of an effective Cartier divisor has dimension one less than the ambient local
ring. In particular, the generic points of its support have codimension one in the ambient
scheme. The comparison uses the closed-immersion stalk map and the nonzerodivisor equation of
the divisor. The dimension formula for the quotient is
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
  obtain ⟨_, ha, hamem, -, ⟨e⟩⟩ := hI.exists_stalkIdeal_eq_span_and_quotient x
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim ha hamem

open Order in
/-- A generic point of an effective Cartier divisor has codimension one in the ambient scheme. -/
theorem IsEffectiveCartier.coheight_subschemeι_of_coheight_eq_zero
    (hI : I.IsEffectiveCartier) {x : I.subscheme} (hx : coheight x = 0) :
    coheight (I.subschemeι x) = 1 := by
  have hdim := hI.ringKrullDim_stalk_add_one x
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx, WithBot.coe_zero,
    zero_add, ← WithBot.coe_one, WithBot.coe_inj] at hdim
  exact hdim.symm

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

open TopologicalSpace Order in
/-- Each point of an effective Cartier divisor lies on the closure of a codimension-one
point of the ambient scheme in the support of the divisor. -/
theorem IsEffectiveCartier.mem_support_iff_exists_codimensionOnePoint (hI : I.IsEffectiveCartier)
    {x : X} :
    x ∈ I.support ↔
      ∃ p : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
        (p : X) ∈ I.support ∧ (p : X) ⤳ x := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hx
    let C : irreducibleComponents I.subscheme :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    let z := genericPoints.ofComponent C
    have hz : IsMax (z : I.subscheme) := by
      intro w hw
      have he := TauCeti.mem_genericPoints_iff.mp z.property w (Scheme.le_iff_specializes.mp hw)
      exact he.le
    refine ⟨⟨I.subschemeι z, hI.coheight_subschemeι_of_coheight_eq_zero hz.coheight_eq_zero⟩,
      ?_, ?_⟩
    · rw [← SetLike.mem_coe, ← I.range_subschemeι]
      exact ⟨z, rfl⟩
    · exact ((genericPoints.isGenericPoint_ofComponent C).specializes
        mem_irreducibleComponent).map I.subschemeι.continuous
  · rintro ⟨p, hp, hpx⟩
    exact hpx.mem_closed I.support.isClosed hp

end AlgebraicGeometry.Scheme.IdealSheafData
