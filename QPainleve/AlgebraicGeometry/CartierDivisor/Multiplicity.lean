/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.Support
public import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.CartierDivisor.Effectivity
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Multiplicities from prime components

On a locally factorial scheme the ideal of an effective Cartier divisor is the
product of its prime ideals with their Weil multiplicities.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] {D : X.IdealSheafData}

local notation "primeIdeal(" q ")" =>
  vanishingIdeal (Closeds.mk (closure {(q : X)}) isClosed_closure)

/-- An effective Cartier ideal on a locally factorial scheme is the product of the prime
divisor ideals with exponents given by the Weil coefficients. The finite set may contain
extra primes with zero coefficient. -/
theorem IsEffectiveCartier.eq_prod_vanishingIdeal_pow (hD : D.IsEffectiveCartier)
    (s : Finset (CodimensionOnePoint X))
    (hs : hD.toCartierDivisor.toWeilDivisor.support ⊆ s) :
    D = ∏ q ∈ s, primeIdeal(q) ^
      (WeilDivisor.coeff hD.toCartierDivisor.toWeilDivisor q).toNat := by
  classical
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let W := hD.toCartierDivisor.toWeilDivisor
  let hP (q : CodimensionOnePoint X) :=
    isEffectiveCartier_vanishingIdeal_closure_singleton q.property
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hD.isEffective_toCartierDivisor
  let hPow (q : CodimensionOnePoint X) (_ : q ∈ s) := TauCeti.isEffectiveCartier_pow (hP q)
    (WeilDivisor.coeff W q).toNat
  apply (hD.toCartierDivisor_eq_iff (TauCeti.isEffectiveCartier_prod hPow)).mp
  apply Scheme.CartierDivisor.toWeilDivisorHom_injective
  rw [toCartierDivisor_prod s hPow, map_sum, Scheme.CartierDivisor.toWeilDivisorHom_apply]
  calc
    _ = ∑ q ∈ s, Finsupp.single q (WeilDivisor.coeff W q) :=
      (Finsupp.sum_single W).symm.trans (Finset.sum_subset hs (fun q _ hq ↦ by
        simp [Finsupp.notMem_support_iff.mp hq]))
    _ = ∑ q ∈ s.attach, Finsupp.single q.val (WeilDivisor.coeff W q.val) :=
      (Finset.sum_attach s _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [toCartierDivisor_pow (hP q.val), map_nsmul,
        Scheme.CartierDivisor.toWeilDivisorHom_apply,
        toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton,
        ← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg (WeilDivisor.coeff_nonneg hW _),
        WeilDivisor.single_eq_zsmul_ofPoint]

/-- Under a dominant morphism, the Weil coefficients of an effective Cartier pullback
are the weighted sums of the coefficients of the pulled-back prime divisors. -/
theorem IsEffectiveCartier.coeff_toWeilDivisor_comap_eq_sum (hD : D.IsEffectiveCartier)
    (s : Finset (CodimensionOnePoint X))
    (hs : hD.toCartierDivisor.toWeilDivisor.support ⊆ s)
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] (f : Y ⟶ X) [IsDominant f]
    (r : CodimensionOnePoint Y) :
    let hT := hD.comap_of_isDominant f
    let hP (q : CodimensionOnePoint X) : ((primeIdeal(q)).comap f).IsEffectiveCartier :=
      (isEffectiveCartier_vanishingIdeal_closure_singleton q.property).comap_of_isDominant f
    WeilDivisor.coeff hT.toCartierDivisor.toWeilDivisor r =
      ∑ q ∈ s, WeilDivisor.coeff hD.toCartierDivisor.toWeilDivisor q *
        WeilDivisor.coeff (hP q).toCartierDivisor.toWeilDivisor r := by
  classical
  intro hT hP
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let W := hD.toCartierDivisor.toWeilDivisor
  let m (q : CodimensionOnePoint X) := (WeilDivisor.coeff W q).toNat
  let hPow (q : CodimensionOnePoint X) (_ : q ∈ s) :=
    TauCeti.isEffectiveCartier_pow (hP q) (m q)
  have hW : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      hD.isEffective_toCartierDivisor
  have hprod : D.comap f = ∏ q ∈ s, (primeIdeal(q)).comap f ^ m q := by
    have h := congrArg (fun J : X.IdealSheafData ↦ J.comap f) (hD.eq_prod_vanishingIdeal_pow s hs)
    simpa only [comap_prod, comap_pow] using h
  have hCartier := (hT.toCartierDivisor_eq_iff (TauCeti.isEffectiveCartier_prod hPow)).mpr hprod
  rw [hCartier, toCartierDivisor_prod s hPow, ← Scheme.CartierDivisor.toWeilDivisorHom_apply,
    map_sum, WeilDivisor.coeff, Finsupp.finsetSum_apply]
  rw [← Finset.sum_attach s (fun q ↦ WeilDivisor.coeff W q *
    WeilDivisor.coeff (hP q).toCartierDivisor.toWeilDivisor r)]
  apply Finset.sum_congr rfl
  intro q _
  rw [toCartierDivisor_pow (hP q.val), map_nsmul, Scheme.CartierDivisor.toWeilDivisorHom_apply,
    ← WeilDivisor.coeff, WeilDivisor.coeff_nsmul]
  exact congrArg (· * WeilDivisor.coeff (hP q.val).toCartierDivisor.toWeilDivisor r)
    (Int.toNat_of_nonneg (WeilDivisor.coeff_nonneg hW q.val))

omit [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)] in
/-- At a prime lying over the isomorphism locus, the coefficient of the pullback agrees
with the coefficient at its image. -/
theorem IsEffectiveCartier.coeff_toWeilDivisor_comap_of_mem_isoLocus
    [IsNormalScheme X] (hD : D.IsEffectiveCartier)
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y] [IsNormalScheme Y] (f : Y ⟶ X)
    (hT : (D.comap f).IsEffectiveCartier) (q : CodimensionOnePoint Y)
    (hq : f q ∈ f.isoLocus) :
    WeilDivisor.coeff hT.toCartierDivisor.toWeilDivisor q =
      WeilDivisor.coeff hD.toCartierDivisor.toWeilDivisor
        ⟨f q, (f.coheight_eq_of_apply_mem_isoLocus hq).trans q.property⟩ := by
  let r : CodimensionOnePoint X :=
    ⟨f q, (f.coheight_eq_of_apply_mem_isoLocus hq).trans q.property⟩
  let : IsDiscreteValuationRing (Y.presheaf.stalk (q : Y)) :=
    IsNormalScheme.isDiscreteValuationRing_stalk q.val q.property
  let : IsDiscreteValuationRing (X.presheaf.stalk (r : X)) :=
    IsNormalScheme.isDiscreteValuationRing_stalk r.val r.property
  let := f.isIso_stalkMap_of_mem_isoLocus hq
  rw [hT.coeff_toWeilDivisor_eq_stalkOrder, hD.coeff_toWeilDivisor_eq_stalkOrder r,
    stalkOrder_comap_of_isIso_stalkMap]

end AlgebraicGeometry.Scheme.IdealSheafData
