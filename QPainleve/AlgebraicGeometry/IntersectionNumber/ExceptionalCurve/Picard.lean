/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Factorial
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# Picard classes of exceptional curves

An exceptional curve of the first kind is determined among integral Cartier divisors
by its Picard class. A distinct prime divisor has nonnegative degree on the exceptional
projective line by `LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_nonneg`.
The exceptional class has degree `-1`.

This is the exceptional-curve rigidity used in Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Proposition 2.6.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry TopologicalSpace
open LineBundleClass (pullback)

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {I J : X.IdealSheafData}

/-- The ideal of an exceptional curve of the first kind equals the ideal of any integral
effective Cartier divisor with the same ideal line-bundle class. -/
theorem eq_of_mk_toInvertibleSheaf_eq (hI : I.IsExceptionalCurveOfFirstKind)
    (hJ : J.IsEffectiveCartier) [IsIntegral J.subscheme]
    (h : LineBundleClass.mk hI.isEffectiveCartier.toInvertibleSheaf =
      LineBundleClass.mk hJ.toInvertibleSheaf) : I = J := by
  have := hI.isIntegral_subscheme
  let p : CodimensionOnePoint X :=
    ⟨I.subschemeι (genericPoint I.subscheme),
      hI.isEffectiveCartier.coheight_subschemeι_genericPoint⟩
  let q : CodimensionOnePoint X :=
    ⟨J.subschemeι (genericPoint J.subscheme), hJ.coheight_subschemeι_genericPoint⟩
  have hp : vanishingIdeal ⟨closure {(p : X)}, isClosed_closure⟩ = I :=
    I.vanishingIdeal_closure_subschemeι_genericPoint
  have hq : vanishingIdeal ⟨closure {(q : X)}, isClosed_closure⟩ = J :=
    J.vanishingIdeal_closure_subschemeι_genericPoint
  by_contra hne
  have hpq : p ≠ q := fun heq ↦ hne (hp.symm.trans (heq ▸ hq))
  have hproper : (J.comap I.subschemeι).IsEffectiveCartier := by
    rw [← hp, ← hq]
    exact (hq.symm ▸ hJ).comap_subschemeι_vanishingIdeal_closure_singleton_of_ne hpq
  obtain ⟨hC, k, _, e, hneg⟩ := isExceptionalCurveOfFirstKind_iff_intersectionNumber.mp hI
  have hnonneg := LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_nonneg k
    (e.hom ≫ I.subschemeι) hJ (by rw [comap_comp]; exact hproper.comap e.hom)
  rw [← h, hneg] at hnonneg
  omega

/-- An isomorphism pulling an integral Cartier ideal class back to an exceptional ideal class
pulls back the ideals themselves. -/
theorem comap_eq_of_pullback_mk_toInvertibleSheaf_eq {Y : Scheme.{u}}
    {J : Y.IdealSheafData} (hI : I.IsExceptionalCurveOfFirstKind)
    (hJ : J.IsEffectiveCartier) [IsIntegral J.subscheme] (e : X ≅ Y)
    (h : pullback e.hom (LineBundleClass.mk hJ.toInvertibleSheaf) =
      LineBundleClass.mk hI.isEffectiveCartier.toInvertibleSheaf) : J.comap e.hom = I := by
  let eJ := J.comapIso e.hom ≪≫ asIso (pullback.snd e.hom J.subschemeι)
  have : IsIntegral (J.comap e.hom).subscheme := .of_isIso eJ.inv
  have hC := hJ.comap e.hom
  rw [hJ.pullback_mk_toInvertibleSheaf hC] at h
  exact (hI.eq_of_mk_toInvertibleSheaf_eq hC h.symm).symm

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
