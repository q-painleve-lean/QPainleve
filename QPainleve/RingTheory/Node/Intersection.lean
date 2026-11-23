/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Unramified.Basic
public import TauCeti.RingTheory.FittingIdeal.Basic
import TauCeti.RingTheory.FittingIdeal.BaseChange
import TauCeti.RingTheory.Kaehler.Hypersurface
import TauCeti.RingTheory.Unramified.LocalRing

/-!
# Intersections of factors of a nodal equation

Two nonunit factors of a hypersurface equation generate the maximal ideal when the
hypersurface has a formally unramified singular subscheme. This is the local
transversality calculation for distinct components of a nodal Cartier divisor.
The singular-subscheme criterion is [Stacks Project, Lemma 53.19.7][Stacks].
We use Tau Ceti's `comap_fittingIdeal_kaehlerDifferential_quotient_span_singleton`
for the hypersurface Jacobian ideal.

[Stacks]: https://stacks.math.columbia.edu/tag/0C4D
-/

public section

open IsLocalRing KaehlerDifferential TauCeti

namespace Module.Basis

/-- In a local algebra with two basic differentials, two nonunit factors whose product
divides a hypersurface equation generate the maximal ideal if the quotient by the first
Fitting ideal of the hypersurface differentials is formally unramified over the field. -/
theorem span_pair_eq_maximalIdeal_of_formallyUnramified
    {k P A : Type*} [Field k] [CommRing P] [IsLocalRing P] [Algebra k P]
    [CommRing A] [IsLocalRing A] [Algebra k A] [Algebra.EssFiniteType k A]
    [Algebra.FormallyUnramified k (A ⧸ fittingIdeal A Ω[A⁄k] 1)]
    (b : Basis (Fin 2) P Ω[P⁄k]) {a c f : P}
    (π : P →ₐ[k] A) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {f})
    (ha : a ∈ maximalIdeal P) (hc : c ∈ maximalIdeal P) (hdiv : a * c ∣ f) :
    Ideal.span {a, c} = maximalIdeal P := by
  let e := (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.EssFiniteType k (P ⧸ Ideal.span {f}) :=
    .of_surjective e.symm.toAlgHom e.symm.surjective
  let J := fittingIdeal A Ω[A⁄k] 1
  let I : Ideal P := Ideal.span {a, c}
  have hI : I ≤ maximalIdeal P := Ideal.span_le.mpr (Set.pair_subset ha hc)
  -- Both the equation and each derivative vanish modulo the ideal of the two factors.
  have hJ : J.comap (π : P →+* A) ≤ I := by
    have hcard : Fintype.card (Fin 2) - 1 = 1 := by simp
    have he : e.toRingHom.comp (Ideal.Quotient.mk _) = (π : P →+* A) := by
      ext x
      rfl
    have hfit : J = (fittingIdeal (P ⧸ Ideal.span {f})
        Ω[(P ⧸ Ideal.span {f})⁄k] 1).map e.toRingHom :=
      fittingIdeal_kaehlerDifferential_eq_map_algEquiv e 1
    rw [← he, ← Ideal.comap_comap, hfit,
      Ideal.comap_map_of_bijective e.toRingHom e.bijective, ← hcard,
      comap_fittingIdeal_kaehlerDifferential_quotient_span_singleton f b]
    apply Ideal.span_le.mpr
    rintro y (rfl | ⟨i, rfl⟩)
    · obtain ⟨r, rfl⟩ := hdiv
      exact I.mul_mem_right r (I.mul_mem_right c (Ideal.subset_span (by simp)))
    · obtain ⟨r, rfl⟩ := hdiv
      let d := (b.coord i).compDer (D k P)
      have haI : a ∈ I := Ideal.subset_span (by simp)
      have hcI : c ∈ I := Ideal.subset_span (by simp)
      have hd : d (a * c * r) ∈ I := by
        simp only [Derivation.leibniz, smul_eq_mul]
        exact I.add_mem (I.mul_mem_right _ (I.mul_mem_right _ haI))
          (I.mul_mem_left _ (I.add_mem (I.mul_mem_right _ haI) (I.mul_mem_right _ hcI)))
      exact hd
  have hproper : J ≠ ⊤ := by
    intro htop
    exact (maximalIdeal.isMaximal P).ne_top (top_le_iff.mp (by simpa [htop] using hJ.trans hI))
  have hmax := Ideal.eq_maximalIdeal_of_formallyUnramified_quotient k hproper
  have hcomap : J.comap (π : P →+* A) = maximalIdeal P := by
    rw [hmax]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hπ)
  exact hI.antisymm (hcomap ▸ hJ)

end Module.Basis
