/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Trivial
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Comparing exceptional divisors under a morphism

An isomorphism between exceptional curves of the first kind identifies their conormal
classes. If the Cartier pullback of the target curve agrees with the source curve
at one stalk on the source curve, the residual divisor is disjoint from the source curve.
The pulled-back ideal then agrees with the source ideal on a neighborhood of the source curve.
Consequently a locally finite type morphism is quasi-finite at every point on the source
curve. This comparison is used in the factorization of proper birational morphisms of
regular surfaces. See the Stacks Project,
[Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {X Y : Scheme.{u}} {E : X.IdealSheafData} {F : Y.IdealSheafData}

/-- An isomorphism of exceptional curves of the first kind identifies their conormal classes. -/
theorem pullback_mk_toInvertibleSheaf_subschemeι
    (hE : E.IsExceptionalCurveOfFirstKind) (hF : F.IsExceptionalCurveOfFirstKind)
    (e : E.subscheme ≅ F.subscheme) :
    LineBundleClass.pullback (e.hom ≫ F.subschemeι)
        (LineBundleClass.mk hF.isEffectiveCartier.toInvertibleSheaf) =
      LineBundleClass.pullback E.subschemeι
        (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) := by
  obtain ⟨k, _, p, -⟩ := hE.exists_iso
  let S := Spec (.of k)
  let π := (projectiveLine k) ↘ S
  let : E.subscheme.Over S := ⟨p.inv ≫ π⟩
  let : F.subscheme.Over S := ⟨e.inv ≫ p.inv ≫ π⟩
  have hp : p.hom ≫ (E.subscheme ↘ S) = π := p.hom_inv_id_assoc π
  have he : e.hom ≫ (F.subscheme ↘ S) = E.subscheme ↘ S :=
    e.hom_inv_id_assoc (p.inv ≫ π)
  have : e.hom.IsOver S := ⟨he⟩
  have hEdeg := hE.intersectionNumber_mk_toInvertibleSheaf k
  have hFdeg := hF.intersectionNumber_mk_toInvertibleSheaf k
  rw [← e.hom.finrank_cohomology_trivial_of_isIso k 0] at hFdeg
  apply (LineBundleClass.pullbackEquiv p).injective
  refine Additive.ofMul.injective ((projectiveLine.picardDegreeEquiv k).injective ?_)
  simp only [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul,
    LineBundleClass.pullbackEquiv_apply]
  rw [LineBundleClass.eulerDegree_pullback_of_isIso p.hom hp,
    LineBundleClass.eulerDegree_pullback_of_isIso p.hom hp,
    ← LineBundleClass.pullback_comp, LineBundleClass.eulerDegree_pullback_of_isIso e.hom he]
  simpa only [LineBundleClass.intersectionNumber_def] using hFdeg.trans hEdeg.symm

/-- Suppose a morphism identifies two exceptional curves of the first kind and its total pullback
of the target divisor is Cartier. If the pulled-back ideal agrees with the source exceptional
ideal at one point of the curve, the residual divisor after subtraction is disjoint from
the entire source exceptional curve. -/
theorem disjoint_support_colon_comap_of_exceptional_curve_isomorphism
    (hE : E.IsExceptionalCurveOfFirstKind) (hF : F.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) (hT : (F.comap f).IsEffectiveCartier)
    (e : E.subscheme ≅ F.subscheme) (he : E.subschemeι ≫ f = e.hom ≫ F.subschemeι)
    (z : E.subscheme)
    (hz : (F.comap f).stalkIdeal (E.subschemeι z) = E.stalkIdeal (E.subschemeι z)) :
    Disjoint (((F.comap f).colon E).support : Set X) (E.support : Set X) := by
  let T := F.comap f
  let R := T.colon E
  have hle : T ≤ E := by
    apply le_map_iff_comap_le.mp
    rw [map, he, Scheme.Hom.ker_comp_of_isIso, F.ker_subschemeι]
  have hR : R.IsEffectiveCartier := hT.colon hE.isEffectiveCartier.locallyPrincipal hle
  have hprod : T = R * E := T.eq_colon_mul E hE.isEffectiveCartier.locallyPrincipal hle
  have hRz : E.subschemeι z ∉ R.support := by
    let x := E.subschemeι z
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
    obtain ⟨a, ha, hspan⟩ := hE.isEffectiveCartier.exists_map_germ_eq_span_singleton
      ⟨U, hU⟩ hxU
    have hmul := congrArg (fun I : X.IdealSheafData ↦ I.stalkIdeal x) hprod
    rw [stalkIdeal_mul, hz, E.stalkIdeal_eq_map ⟨U, hU⟩ x hxU, hspan] at hmul
    rw [R.mem_support_iff_stalkIdeal_ne_top, not_not]
    apply ha.span_singleton_mul_right_inj.mp
    simpa only [mul_comm (Ideal.span {a}), Ideal.top_mul] using hmul.symm
  -- The residual pulls back to an effective Cartier divisor on the source curve.
  have := hE.isIntegral_subscheme
  have hRη : E.subschemeι (genericPoint E.subscheme) ∉ R.support :=
    (genericPoint_specializes z).map E.subschemeι.continuous |>.mem_open
      R.support.isClosed.isOpen_compl hRz
  have hRC : (R.comap E.subschemeι).IsEffectiveCartier :=
    hR.comap_of_isIntegral _ hRη
  have hC := hR.pullback_mk_toInvertibleSheaf hRC
  have hcompare : LineBundleClass.pullback E.subschemeι
      (LineBundleClass.mk hT.toInvertibleSheaf) =
        LineBundleClass.pullback E.subschemeι
          (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) := by
    rw [← hF.isEffectiveCartier.pullback_mk_toInvertibleSheaf hT,
      LineBundleClass.pullback_comp, he]
    exact hE.pullback_mk_toInvertibleSheaf_subschemeι hF e
  have hmul : LineBundleClass.mk hT.toInvertibleSheaf =
      LineBundleClass.mk hR.toInvertibleSheaf *
        LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf :=
    (LineBundleClass.mk_toInvertibleSheaf_congr hT
      (TauCeti.isEffectiveCartier_mul hR hE.isEffectiveCartier) hprod).trans
        (LineBundleClass.mk_toInvertibleSheaf_mul hR hE.isEffectiveCartier)
  -- The two equal conormal classes cancel, leaving a trivial residual ideal bundle.
  rw [hmul, LineBundleClass.pullback_mul, hC, mul_eq_right] at hcompare
  have htop := hRC.eq_top_of_isField_of_mk_toInvertibleSheaf_eq_one
    hE.isField_globalSections hcompare
  refine Set.disjoint_left.mpr fun x hxR hxE ↦ ?_
  rw [← E.range_subschemeι] at hxE
  obtain ⟨w, rfl⟩ := hxE
  have hw : w ∈ ((R.comap E.subschemeι).support : Set E.subscheme) := by
    rw [support_comap, Closeds.coe_preimage, Set.mem_preimage]
    exact hxR
  simp only [htop, support_top, Closeds.coe_bot, Set.mem_empty_iff_false] at hw

/-- If a locally finite type morphism identifies two exceptional curves of the first kind
and the Cartier pullback agrees with the source exceptional ideal at one stalk on the
curve, the morphism is quasi-finite at every point of that curve. -/
theorem quasiFiniteAt_of_exceptional_curve_isomorphism
    (hE : E.IsExceptionalCurveOfFirstKind) (hF : F.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hT : (F.comap f).IsEffectiveCartier)
    (e : E.subscheme ≅ F.subscheme) (he : E.subschemeι ≫ f = e.hom ≫ F.subschemeι)
    (z₀ : E.subscheme)
    (hz₀ : (F.comap f).stalkIdeal (E.subschemeι z₀) = E.stalkIdeal (E.subschemeι z₀))
    (z : E.subscheme) :
    f.QuasiFiniteAt (E.subschemeι z) := by
  let T := F.comap f
  let R := T.colon E
  have hd : Disjoint (R.support : Set X) (E.support : Set X) :=
    hE.disjoint_support_colon_comap_of_exceptional_curve_isomorphism hF f hT e he z₀ hz₀
  have hle : T ≤ E := by
    apply le_map_iff_comap_le.mp
    rw [map, he, Scheme.Hom.ker_comp_of_isIso, F.ker_subschemeι]
  have hprod : T.support = R.support ⊔ E.support :=
    (congrArg support (T.eq_colon_mul E hE.isEffectiveCartier.locallyPrincipal hle)).trans
      (support_mul R E)
  let x := E.subschemeι z
  let y := f x
  have hx : x ∈ (E.support : Set X) := E.range_subschemeι ▸ Set.mem_range_self z
  apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
  have hfiber : (f.fiberι y) ⁻¹' (R.support.compl : Set X) = {f.asFiber x} := by
    ext w
    rw [Set.mem_singleton_iff, Set.mem_preimage, Closeds.coe_compl, Set.mem_compl_iff]
    constructor
    · intro hw
      have hy : f (f.fiberι y w) = y := (f.fiberHomeo y w).property
      have hyF : y ∈ (F.support : Set Y) := by
        rw [← F.range_subschemeι]
        exact ⟨e.hom z, (congrArg (fun a : E.subscheme ⟶ Y ↦ a z) he).symm⟩
      have hTw : f.fiberι y w ∈ (T.support : Set X) := by
        simp only [T, support_comap, Closeds.coe_preimage, Set.mem_preimage, hy]
        exact hyF
      rw [hprod, Closeds.coe_sup, Set.mem_union] at hTw
      have hEw : f.fiberι y w ∈ (E.support : Set X) := hTw.resolve_left hw
      obtain ⟨v, hv⟩ := E.range_subschemeι.symm ▸ hEw
      have hEq : f (E.subschemeι v) = f (E.subschemeι z) := (congrArg f hv).trans hy
      have hvz : v = z := (e.hom ≫ F.subschemeι).injective
        ((congrArg (fun a : E.subscheme ⟶ Y ↦ a v) he).symm.trans
          (hEq.trans (congrArg (fun a : E.subscheme ⟶ Y ↦ a z) he)))
      exact (f.fiberι y).injective
        (hv.symm.trans ((congrArg E.subschemeι hvz).trans (f.fiberι_asFiber x).symm))
    · rintro rfl
      rw [f.fiberι_asFiber]
      exact fun hr ↦ Set.disjoint_left.mp hd hr hx
  rw [← hfiber]
  exact R.support.compl.isOpen.preimage (f.fiberι y).continuous

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

variable {X Y : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData}

/-- If a dominant morphism identifies two exceptional curves of the first kind and induces an
isomorphism on ambient stalks at one point of the source curve, then on a neighborhood of that
curve the inverse image of the target curve is exactly the source curve as a closed subscheme. -/
theorem exists_comap_eq_on_open_of_isExceptionalCurveOfFirstKind
    (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (hI : I.IsExceptionalCurveOfFirstKind) (hJ : J.IsExceptionalCurveOfFirstKind)
    (g : I.subscheme ⟶ J.subscheme) [IsIso g]
    (w : I.subschemeι ≫ f = g ≫ J.subschemeι)
    (z₀ : I.subscheme) [IsIso (f.stalkMap (I.subschemeι z₀))] :
    ∃ U : X.Opens, (I.support : Set X) ⊆ U ∧ (J.comap f).comap U.ι = I.comap U.ι := by
  have hle : J.comap f ≤ I := le_map_iff_comap_le.mp (by
    rw [IdealSheafData.map, w, Scheme.Hom.ker_comp_of_isIso, ker_subschemeι])
  have hD : (J.comap f).IsEffectiveCartier := by
    apply hJ.isEffectiveCartier.comap_of_isIntegral f
    rw [f.genericPoint_eq_of_isDominant]
    exact hJ.isEffectiveCartier.genericPoint_notMem_support
  let R := (J.comap f).colon I
  have hprod : J.comap f = R * I :=
    (J.comap f).eq_colon_mul I hI.isEffectiveCartier.locallyPrincipal hle
  have hd : Disjoint (R.support : Set X) (I.support : Set X) :=
    hI.disjoint_support_colon_comap_of_exceptional_curve_isomorphism hJ f hD (asIso g) w z₀
      (J.stalkIdeal_comap_eq_of_isIso_stalkMap f g w z₀)
  refine ⟨R.support.compl, ?_, ?_⟩
  · intro x hx hxR
    exact Set.disjoint_left.mp hd hxR hx
  · rw [hprod, comap_mul, (comap_eq_top_iff _ _).mpr
      (Scheme.Opens.ι_preimage_self _), ← one_eq_top, one_mul]

end AlgebraicGeometry.Scheme.Hom
