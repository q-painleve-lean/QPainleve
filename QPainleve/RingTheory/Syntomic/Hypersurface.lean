/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import TauCeti.RingTheory.Syntomic.StandardSyntomic

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# Hypersurfaces in standard smooth algebras

Over a field, a nonempty hypersurface cut out by a nonzerodivisor in a standard smooth
algebra is standard syntomic of relative dimension one less than the ambient dimension.
-/

public section

open MvPolynomial TauCeti
open scoped nonZeroDivisors

namespace QPainleve

universe u v

/-- A nonempty Cartier hypersurface in a standard smooth algebra over a field is standard
syntomic of relative dimension one less than the ambient dimension. -/
theorem isStandardSyntomicOfRelativeDimension_quotient_span_singleton
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] {n : ℕ} [hA : Algebra.IsStandardSmoothOfRelativeDimension (n + 1) k A]
    {f : A} (hf : f ∈ A⁰) [Nontrivial (A ⧸ Ideal.span {f})] :
    TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension n k (A ⧸ Ideal.span {f}) := by
  have : Nontrivial A := (Ideal.Quotient.mk (Ideal.span {f})).domain_nontrivial
  obtain ⟨ι, σ, _, _, P, hP⟩ := hA.out
  let B := A ⧸ Ideal.span {f}
  let G : Algebra.Generators A B PEmpty.{1} :=
    .ofSurjectiveAlgebraMap Ideal.Quotient.mk_surjective
  let Q : Algebra.Presentation A B PEmpty.{1} Unit := {
    toGenerators := G
    relation _ := C f
    span_range_relation_eq_ker := by
      have ha : aeval G.val = (Ideal.Quotient.mkₐ A (Ideal.span {f})).comp
          (isEmptyAlgEquiv A PEmpty).toAlgHom := by
        ext j
        exact PEmpty.elim j
      let e := (isEmptyAlgEquiv A PEmpty).toRingEquiv
      have hk : G.ker = (Ideal.span {f}).comap e := by
        rw [G.ker_eq_ker_aeval_val, ha]
        exact (RingHom.comap_ker (Ideal.Quotient.mk (Ideal.span {f})) e.toRingHom).symm.trans
          (congrArg (Ideal.comap e.toRingHom) (Ideal.mk_ker))
      rw [hk, ← Ideal.map_symm e, Ideal.map_span, Set.image_singleton]
      rw [show e.symm f = C f from isEmptyAlgEquiv_symm_apply A f, Set.range_const] }
  apply (Q.comp P.toPresentation).isStandardSyntomicOfRelativeDimension_of_ringKrullDim_le
  · simp only [Nat.card_sum, Nat.card_unique, Nat.card_of_isEmpty, zero_add]
    simp only [Algebra.Presentation.dimension] at hP
    omega
  · have hdim := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hf
    rw [ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension k (S := A) (n + 1)] at hdim
    apply (ENat.WithBot.add_le_add_natCast_right_iff (c := 1)).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hdim

end QPainleve
