/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local equations and multiplicity of effective Cartier divisors

The local ring of an effective Cartier divisor is the quotient of the ambient stalk
by a nonzerodivisor equation. In a regular ambient stalk the divisor has multiplicity one
exactly when its local ring is regular. The comparison uses Tau Ceti's
`IsRegularLocalRing.quotient_span_singleton_iff`.
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData}

/-- A point of an effective Cartier divisor has a nonzerodivisor equation in the ambient
maximal ideal, and its local ring is the quotient by that equation. -/
theorem IsEffectiveCartier.exists_stalkIdeal_eq_span_and_quotient
    (hD : D.IsEffectiveCartier) (q : D.subscheme) :
    let R := X.presheaf.stalk (D.subschemeι q)
    ∃ a : R, IsSMulRegular R a ∧ a ∈ IsLocalRing.maximalIdeal R ∧
      D.stalkIdeal (D.subschemeι q) = Ideal.span {a} ∧
      Nonempty ((R ⧸ Ideal.span {a}) ≃+* D.subscheme.presheaf.stalk q) := by
  let p := D.subschemeι q
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top p)
  obtain ⟨a, ha, hspan⟩ := hD.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hpU
  have hDspan : D.stalkIdeal p = Ideal.span {a} :=
    (D.stalkIdeal_eq_map ⟨U, hU⟩ p hpU).trans hspan
  let f := (D.subschemeι.stalkMap q).hom
  have hf : Function.Surjective f := D.subschemeι.stalkMap_surjective q
  have hker : RingHom.ker f = Ideal.span {a} := by
    rw [D.subschemeι.ker_stalkMap_of_isClosedImmersion, ker_subschemeι]
    exact hDspan
  have haMem : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f))
      (hker ▸ Ideal.mem_span_singleton_self a)
  exact ⟨a, ha, haMem, hDspan,
    ⟨(Ideal.quotEquivOfEq hker.symm).trans (f.quotientKerEquivOfSurjective hf)⟩⟩

/-- An effective Cartier divisor has order one at a point of its support in a regular
ambient stalk exactly when the divisor's own stalk is regular. -/
theorem IsEffectiveCartier.stalkOrder_eq_one_iff_isRegularLocalRing
    (hD : D.IsEffectiveCartier) (q : D.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (D.subschemeι q))] :
    D.stalkOrder (D.subschemeι q) = 1 ↔
      IsRegularLocalRing (D.subscheme.presheaf.stalk q) := by
  let p := D.subschemeι q
  obtain ⟨a, ha, haMem, hDspan, ⟨e⟩⟩ := hD.exists_stalkIdeal_eq_span_and_quotient q
  have hregular : IsRegularLocalRing (D.subscheme.presheaf.stalk q) ↔
      a ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ 2 :=
    ⟨fun h ↦ (TauCeti.IsRegularLocalRing.quotient_span_singleton_iff
      haMem ha.isLeftRegular.ne_zero).mp (IsRegularLocalRing.of_ringEquiv e.symm),
      fun h ↦
        have := (TauCeti.IsRegularLocalRing.quotient_span_singleton_iff
          haMem ha.isLeftRegular.ne_zero).mpr h
        IsRegularLocalRing.of_ringEquiv e⟩
  have hp : p ∈ (D.support : Set X) := D.range_subschemeι ▸ Set.mem_range_self q
  have h₁ := (D.one_le_stalkOrder_iff p).mpr hp
  have h₂ : (1 : ℕ∞) < D.stalkOrder p ↔
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ 2 := by
    have h := D.natCast_le_stalkOrder_iff p 2
    rw [hDspan, Ideal.span_singleton_le_iff_mem] at h
    have he := ENat.natCast_add_one_le_iff (m := 1) (n := D.stalkOrder p)
    rw [← Nat.cast_add_one] at he
    exact he.symm.trans h
  refine ⟨fun h ↦ hregular.mpr (fun ha ↦ ?_), fun h ↦ ?_⟩
  · have hl := h₂.mpr ha
    rw [h] at hl
    exact (lt_irrefl _) hl
  · exact le_antisymm (not_lt.mp (h₂.not.mpr (hregular.mp h))) h₁

end AlgebraicGeometry.Scheme.IdealSheafData
