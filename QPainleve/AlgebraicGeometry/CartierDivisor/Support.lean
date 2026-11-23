/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Support of effective Cartier divisors

The stalk ideal of an effective Cartier divisor detects its prime components. At
codimension one, membership in its support is equivalent to having nonzero Weil coefficient.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The ideal of an effective Cartier divisor is nonzero at every stalk. -/
theorem stalkIdeal_ne_bot (hI : I.IsEffectiveCartier) (x : X) : I.stalkIdeal x ≠ ⊥ := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (TopologicalSpace.Opens.mem_top x)
  obtain ⟨a, ha, hspan⟩ := hI.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hx
  rw [I.stalkIdeal_eq_map ⟨U, hU⟩ x hx, hspan]
  exact fun h ↦ ha.isLeftRegular.ne_zero (Ideal.span_singleton_eq_bot.mp h)

/-- A reduced effective Cartier divisor has multiplicity at most one at a discrete
valuation stalk. -/
theorem stalkOrder_le_one_of_isReduced (hI : I.IsEffectiveCartier) [IsReduced I.subscheme]
    (x : X) [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    I.stalkOrder x ≤ 1 := by
  by_cases hx : x ∈ I.support
  · have hxRange : x ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hx
    obtain ⟨q, rfl⟩ := hxRange
    let R := X.presheaf.stalk (I.subschemeι q)
    let P := IsLocalRing.maximalIdeal R
    have hrad : (I.stalkIdeal (I.subschemeι q)).IsRadical := by
      have hk := (RingHom.ker_isRadical_iff_reduced_of_surjective
        (I.subschemeι.stalkMap_surjective q)).mpr inferInstance
      simpa only [I.subschemeι.ker_stalkMap_of_isClosedImmersion q, I.ker_subschemeι] using hk
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (hI.stalkIdeal_ne_bot (I.subschemeι q)) ht
    rw [← Ideal.span_singleton_pow, ← ht.maximalIdeal_eq] at hn
    have hn₀ : n ≠ 0 := by
      rintro rfl
      exact (I.mem_support_iff_stalkIdeal_ne_top _).mp hx (hn.trans (by simp))
    have heq : I.stalkIdeal (I.subschemeι q) = P := by
      rw [← hrad.radical, hn, Ideal.radical_pow _ hn₀,
        (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]
    by_contra! h
    have htwo : (2 : ℕ∞) ≤ I.stalkOrder (I.subschemeι q) := by
      simpa only [Nat.cast_one, one_add_one_eq_two] using
        (ENat.natCast_add_one_le_iff (m := 1)).mpr h
    have hle := (I.natCast_le_stalkOrder_iff (I.subschemeι q) 2).mp htwo
    rw [heq, ← pow_one P, ← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe,
      ← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe] at hle
    have hbad := (IsDiscreteValuationRing.idealOrderIsoENat R).symm.le_iff_le.mp hle
    exact (by decide : ¬ ((1 : ℕ∞ᵒᵈ) ≤ 2)) hbad
  · rw [(I.stalkOrder_eq_zero_iff x).mpr hx]
    exact zero_le_one

variable [IsIntegral X]

/-- The generic point is outside the support of an effective Cartier divisor. -/
theorem genericPoint_notMem_support (hI : I.IsEffectiveCartier) : genericPoint X ∉ I.support := by
  rw [I.mem_support_iff_stalkIdeal_ne_top, not_not]
  let : Field X.functionField := inferInstance
  exact (eq_bot_or_eq_top (I.stalkIdeal (genericPoint X))).resolve_left
    (hI.stalkIdeal_ne_bot (genericPoint X))

/-- The pullback of an effective Cartier divisor along a dominant morphism of integral
schemes is effective Cartier. -/
theorem comap_of_isDominant {Y : Scheme.{u}} (hI : I.IsEffectiveCartier) (f : Y ⟶ X)
    [IsIntegral Y] [IsDominant f] : (I.comap f).IsEffectiveCartier :=
  hI.comap_of_isIntegral f (f.genericPoint_eq_of_isDominant.symm ▸ hI.genericPoint_notMem_support)

open TauCeti.AlgebraicGeometry in
/-- At a codimension-one discrete valuation stalk, the Weil coefficient of an effective
Cartier divisor is the order of its ideal. -/
theorem coeff_toWeilDivisor_eq_stalkOrder [IsNoetherian X] (hI : I.IsEffectiveCartier)
    (x : CodimensionOnePoint X) [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor x = (I.stalkOrder (x : X)).toNat := by
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI (x : X)
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  rw [hI.toCartierDivisor.coeff_toWeilDivisor_eq_ord x hxU _
      (hI.toCartierDivisor_restrict U ha.isLeftRegular.ne_zero hUa).symm,
    Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hxU a,
    Scheme.ord_algebraMap_stalk x.property, Ring.ord_eq_addVal]
  congr 2
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [I.natCast_le_stalkOrder_iff, I.stalkIdeal_eq_map U x hxU, hUa, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  exact (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal).symm

open TauCeti.AlgebraicGeometry in
/-- At a codimension-one point, the Weil coefficient of an effective Cartier divisor
vanishes exactly where its ideal is the unit ideal. -/
theorem coeff_toWeilDivisor_eq_zero_iff [IsNoetherian X] (hI : I.IsEffectiveCartier)
    (x : CodimensionOnePoint X) :
    WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor x = 0 ↔ (x : X) ∉ I.support := by
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI (x : X)
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  have ha0 : a ≠ 0 := ha.isLeftRegular.ne_zero
  rw [hI.toCartierDivisor.coeff_toWeilDivisor_eq_ord x hxU _
      (hI.toCartierDivisor_restrict U ha0 hUa).symm,
    Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hxU a]
  have hb : (X.presheaf.germ U.val x hxU).hom a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr ha0
  rw [Scheme.ord_algebraMap_stalk_eq_zero_iff x.property specializes_rfl hb,
    I.mem_support_iff_stalkIdeal_ne_top, not_not, I.stalkIdeal_eq_map U x hxU, hUa,
    Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
