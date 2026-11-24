/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Picard
public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral

/-!
# Exceptional curves in a boundary

The class of an exceptional curve of the first kind detects whether the curve
is supported on a specified boundary. This lets a Picard isometry which matches
the boundary classes distinguish internal exceptional curves from exceptional
boundary components.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry TopologicalSpace
open LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  [∀ x : X, IsDomain (X.presheaf.stalk x)]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {E D : X.IdealSheafData}

/-- An exceptional curve is supported on a boundary exactly when its divisor
class is one of the prime divisor classes of that boundary. -/
theorem support_le_iff_exists_boundaryPrime_class_eq (hE : E.IsExceptionalCurveOfFirstKind) :
    E.support ≤ D.support ↔ ∃ p : D.boundaryPrimes,
      primeDivisorClass (D.boundaryPrimeEmbedding p) =
        (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf)⁻¹ := by
  have : IsIntegral E.subscheme := hE.isIntegral_subscheme
  constructor
  · intro h
    let x := E.subschemeι (genericPoint E.subscheme)
    have hx : x ∈ E.support := by
      rw [← SetLike.mem_coe, ← E.range_subschemeι]
      exact Set.mem_range_self _
    let p : D.boundaryPrimes :=
      ⟨x, mem_boundaryPrimes.mpr ⟨h hx, hE.isEffectiveCartier.coheight_subschemeι_genericPoint⟩⟩
    refine ⟨p, ?_⟩
    exact (primeDivisorClass_def _).trans (congrArg Inv.inv
      (mk_toInvertibleSheaf_congr _ hE.isEffectiveCartier (by
        rw [coe_boundaryPrimeEmbedding]
        exact E.vanishingIdeal_closure_subschemeι_genericPoint)))
  · rintro ⟨p, hp⟩
    let q := D.boundaryPrimeEmbedding p
    let J := vanishingIdeal (⟨closure {(q : X)}, isClosed_closure⟩ : Closeds X)
    have hJ : J.IsEffectiveCartier := isEffectiveCartier_vanishingIdeal_closure_singleton q.property
    have hclass : LineBundleClass.mk hJ.toInvertibleSheaf =
        LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf := by
      apply inv_injective
      exact (primeDivisorClass_def q).symm.trans hp
    rw [hE.eq_of_mk_toInvertibleSheaf_eq hJ hclass.symm, ← SetLike.coe_subset_coe,
      coe_support_vanishingIdeal]
    exact closure_minimal (Set.singleton_subset_iff.mpr (by
      simpa only [q, coe_boundaryPrimeEmbedding, SetLike.mem_coe] using
        (mem_boundaryPrimes.mp p.property).1))
      D.support.isClosed

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
