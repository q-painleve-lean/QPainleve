/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
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

open TauCeti.AlgebraicGeometry in
/-- A prime component of a reduced effective Cartier divisor has Weil coefficient one. -/
theorem coeff_toWeilDivisor_eq_one_of_isReduced [IsNoetherian X] (hI : I.IsEffectiveCartier)
    [IsReduced I.subscheme] (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (hx : (x : X) ∈ I.support) :
    WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor x = 1 := by
  have hne : WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor x ≠ 0 :=
    fun hz ↦ (hI.coeff_toWeilDivisor_eq_zero_iff x).mp hz hx
  rw [hI.coeff_toWeilDivisor_eq_stalkOrder x] at hne ⊢
  have hle := ENat.toNat_le_of_le_natCast (hI.stalkOrder_le_one_of_isReduced x)
  omega

open TauCeti.AlgebraicGeometry in
/-- The Weil divisor of a reduced effective Cartier divisor is the sum of its
distinct prime components. -/
theorem toWeilDivisor_eq_sum_single_of_isReduced [IsNoetherian X] (hI : I.IsEffectiveCartier)
    [IsReduced I.subscheme] [∀ x : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    {ι : Type*} [Fintype ι] (p : ι ↪ CodimensionOnePoint X)
    (hp : ∀ x : CodimensionOnePoint X, (x : X) ∈ I.support ↔ x ∈ Set.range p) :
    hI.toCartierDivisor.toWeilDivisor = ∑ i, Finsupp.single (p i) 1 := by
  classical
  apply Finsupp.ext
  intro x
  rw [Finsupp.finsetSum_apply]
  by_cases hx : x ∈ Set.range p
  · obtain ⟨j, rfl⟩ := hx
    rw [← WeilDivisor.coeff, hI.coeff_toWeilDivisor_eq_one_of_isReduced _ ((hp _).mpr
      (Set.mem_range_self j))]
    simp [Finsupp.single_apply, p.injective.eq_iff]
  · rw [← WeilDivisor.coeff, (hI.coeff_toWeilDivisor_eq_zero_iff x).mpr (fun h ↦ hx ((hp x).mp h))]
    have hn (i : ι) : p i ≠ x := fun he ↦ hx ⟨i, he⟩
    simp [hn]

open TauCeti.AlgebraicGeometry LineBundleClass in
/-- The Picard class of a reduced effective Cartier divisor is the sum of the classes
of its distinct prime components. -/
theorem ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass [IsNoetherian X]
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hI : I.IsEffectiveCartier) [IsReduced I.subscheme]
    {ι : Type*} [Fintype ι] (p : ι ↪ CodimensionOnePoint X)
    (hp : ∀ x : CodimensionOnePoint X, (x : X) ∈ I.support ↔ x ∈ Set.range p) :
    Additive.ofMul (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      ∑ i, Additive.ofMul (primeDivisorClass (p i)) := by
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : ∀ q : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (q : X)) :=
    fun q ↦ IsNormalScheme.isDiscreteValuationRing_stalk q.val q.property
  have h := congrArg (Scheme.CartierDivisor.weilToLineBundleClassHom X)
    (hI.toWeilDivisor_eq_sum_single_of_isReduced p hp)
  rw [Scheme.CartierDivisor.weilToLineBundleClassHom_toWeilDivisor,
    hI.toLineBundleClass_toCartierDivisor, map_sum] at h
  simpa only [Scheme.CartierDivisor.weilToLineBundleClassHom_single,
    ← LineBundleClass.primeDivisorClass_def, one_zsmul] using h

open TauCeti.AlgebraicGeometry in
/-- A principal equation on an affine open immersion computes the Weil coefficient of an
effective Cartier divisor at the image of a codimension-one point. -/
theorem coeff_toWeilDivisor_eq_ord_of_comap_eq_span_singleton [IsNoetherian X]
    (hI : I.IsEffectiveCartier) {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) [IsOpenImmersion j] (y : CodimensionOnePoint Y)
    (b : Γ(Y, ⊤)) (hb : I.comap j = ofIdealTop (Ideal.span {b})) :
    WeilDivisor.coeff hI.toCartierDivisor.toWeilDivisor (y.mapOfIsOpenImmersion j) =
      Y.ord (Y.germToFunctionField ⊤ b) y := by
  let x := y.mapOfIsOpenImmersion j
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI (x : X)
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  -- The two chart equations generate the same ideal after passage to the stalk on Y.
  have hspan := congrArg (fun J : Y.IdealSheafData ↦ J.stalkIdeal y) hb
  have hyU : j y ∈ U.val := by
    simpa only [x, CodimensionOnePoint.coe_mapOfIsOpenImmersion] using hxU
  rw [I.stalkIdeal_comap, I.stalkIdeal_eq_map U (j y) hyU, hUa, Ideal.map_span,
    Set.image_singleton, Ideal.map_span, Set.image_singleton] at hspan
  rw [stalkIdeal_eq_map _ ⟨⊤, isAffineOpen_top Y⟩ _ trivial,
    ← equivOfIsAffine_apply, ← equivOfIsAffine_symm_apply,
    OrderRingIso.apply_symm_apply, Ideal.map_span, Set.image_singleton] at hspan
  rw [hI.toCartierDivisor.coeff_toWeilDivisor_eq_ord x hxU _
    (hI.toCartierDivisor_restrict U ha.isLeftRegular.ne_zero hUa).symm, Units.val_mk0]
  simp only [x, CodimensionOnePoint.coe_mapOfIsOpenImmersion]
  rw [← Scheme.ord_functionFieldMap j _ (y : Y),
    ← X.algebraMap_germ_eq_germToFunctionField hyU,
    j.functionFieldMap_algebraMap_stalk,
    ← Y.algebraMap_germ_eq_germToFunctionField (Opens.mem_top (y : Y)),
    Scheme.ord_algebraMap_stalk y.property, Scheme.ord_algebraMap_stalk y.property,
    Ring.ord, Ring.ord, hspan]

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
