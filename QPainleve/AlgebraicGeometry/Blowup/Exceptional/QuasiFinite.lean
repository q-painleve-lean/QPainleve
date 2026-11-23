/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.Pullback
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Quasi-finiteness along exceptional curves

Suppose a dominant morphism of integral schemes identifies two exceptional curves of the first
kind and induces an isomorphism of ambient local rings at one point of the source curve. The
target curve pulls back to the source curve on a neighborhood of the latter. In particular, a
finite-type morphism satisfying these conditions is quasi-finite at every point on the curve.

This is the exceptional-curve comparison in the proof of
[Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R). The residual divisor
after subtracting the source exceptional curve has zero intersection with it, by the two
conormal degrees. The proof uses Tau Ceti's Cartier subtraction and restriction degrees.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} {I : X.IdealSheafData} {J : Y.IdealSheafData}

private theorem intersectionNumber_comap_eq_of_isExceptionalCurveOfFirstKind
    (hI : I.IsExceptionalCurveOfFirstKind) (hJ : J.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) (g : I.subscheme ⟶ J.subscheme) [IsIso g]
    (w : I.subschemeι ≫ f = g ≫ J.subschemeι) {k : Type u} [Field k]
    [I.subscheme.Over (Spec (.of k))] (hD : (J.comap f).IsEffectiveCartier) :
    LineBundleClass.intersectionNumber k I.subschemeι (LineBundleClass.mk hD.toInvertibleSheaf) =
    LineBundleClass.intersectionNumber k I.subschemeι
      (LineBundleClass.mk hI.isEffectiveCartier.toInvertibleSheaf) := by
  let : J.subscheme.Over (Spec (.of k)) := ⟨inv g ≫ I.subscheme ↘ Spec (.of k)⟩
  have : g.IsOver (Spec (.of k)) := ⟨by
    -- Transport the structure morphism over the field through the curve isomorphism.
    change g ≫ inv g ≫ _ = _
    simp⟩
  rw [← hJ.isEffectiveCartier.pullback_mk_toInvertibleSheaf hD,
    LineBundleClass.intersectionNumber_pullback, w, ← LineBundleClass.intersectionNumber_pullback,
    LineBundleClass.intersectionNumber_def, LineBundleClass.eulerDegree_pullback_of_isIso g
      (comp_over g _), ← LineBundleClass.intersectionNumber_def,
    hI.intersectionNumber_mk_toInvertibleSheaf, hJ.intersectionNumber_mk_toInvertibleSheaf,
    g.finrank_cohomology_trivial_of_isIso k 0]

private theorem notMem_support_residual_of_isExceptionalCurveOfFirstKind
    (hI : I.IsExceptionalCurveOfFirstKind) (hJ : J.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) (g : I.subscheme ⟶ J.subscheme) [IsIso g]
    (w : I.subschemeι ≫ f = g ≫ J.subschemeι)
    (hD : (J.comap f).IsEffectiveCartier) {D : X.IdealSheafData} (hR : D.IsEffectiveCartier)
    (hprod : J.comap f = D * I) (z₀ : I.subscheme) (hz₀ : I.subschemeι z₀ ∉ D.support)
    (z : I.subscheme) : I.subschemeι z ∉ D.support := by
  have := hI.isIntegral_subscheme
  obtain ⟨k, _, e, -⟩ := hI.exists_iso
  let : I.subscheme.Over (Spec (.of k)) :=
    ⟨e.inv ≫ projectiveLine k ↘ Spec (.of k)⟩
  have : e.inv.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (I.subscheme ↘ Spec (.of k)) := by
    -- The structure morphism factors through the chosen projective-line isomorphism.
    change IsProper (e.inv ≫ projectiveLine k ↘ Spec (.of k))
    infer_instance
  have : RelativeDimensionLE 1 (I.subscheme ↘ Spec (.of k)) :=
    RelativeDimensionLE.isPreimmersion_comp e.inv (projectiveLine k ↘ Spec (.of k))
  have hfin (n : ℕ) : FiniteDimensional k
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (InvertibleSheaf.trivial I.subscheme).obj n) :=
    FiniteDimensional.of_injective _ (e.inv.cohomologyTrivialBaseLinearEquivOfIsIso k n).injective
  have := hfin 0
  have := hfin 1
  have hproper : (D.comap I.subschemeι).IsEffectiveCartier := by
    refine hR.comap_of_isIntegral _ fun h ↦ hz₀ ?_
    exact specializes_iff_forall_closed.mp
      (((genericPoint_spec I.subscheme).specializes (Set.mem_univ z₀)).map I.subschemeι.continuous)
      _ D.support.isClosed h
  have hdeg := intersectionNumber_comap_eq_of_isExceptionalCurveOfFirstKind hI hJ f g w hD
    (k := k)
  have hclass : LineBundleClass.mk hD.toInvertibleSheaf =
      LineBundleClass.mk hR.toInvertibleSheaf *
        LineBundleClass.mk hI.isEffectiveCartier.toInvertibleSheaf := by
    generalize J.comap f = A at hprod hD
    subst A
    exact LineBundleClass.mk_toInvertibleSheaf_mul hR hI.isEffectiveCartier
  rw [hclass, LineBundleClass.intersectionNumber_mul_of_isIntegral] at hdeg
  have hzero := add_right_cancel (hdeg.trans (zero_add _).symm)
  have hpos := LineBundleClass.intersectionNumber_inv_mk_toInvertibleSheaf_pos_iff
    k I.subschemeι hR hproper
  rw [LineBundleClass.intersectionNumber_inv_of_isIntegral, hzero, neg_zero] at hpos
  exact fun hz ↦ (lt_irrefl 0) (hpos.mpr ⟨z, hz⟩)

end AlgebraicGeometry.Scheme.IdealSheafData

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
  obtain ⟨D, hR, hprod⟩ :=
    (hD.le_iff_exists_eq_mul hI.isEffectiveCartier.locallyPrincipal).mp hle
  have hz₀ : I.subschemeι z₀ ∉ D.support := by
    have hstalk := J.stalkIdeal_comap_eq_of_isIso_stalkMap f g w z₀
    rw [hprod, stalkIdeal_mul, mul_comm] at hstalk
    obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
      (Opens.mem_top (I.subschemeι z₀))
    obtain ⟨a, ha, hspan⟩ :=
      hI.isEffectiveCartier.exists_map_germ_eq_span_singleton ⟨U, hU⟩ hzU
    rw [← I.stalkIdeal_eq_map ⟨U, hU⟩ _ hzU] at hspan
    rw [hspan] at hstalk
    rw [mem_support_iff_stalkIdeal_ne_top, not_not]
    apply ha.span_singleton_mul_right_inj.mp
    simpa only [Ideal.mul_top] using hstalk
  refine ⟨D.support.compl, ?_, ?_⟩
  · rw [← range_subschemeι]
    rintro _ ⟨z, rfl⟩
    exact notMem_support_residual_of_isExceptionalCurveOfFirstKind
      hI hJ f g w hD hR hprod z₀ hz₀ z
  · rw [hprod, comap_mul, (comap_eq_top_iff _ _).mpr
      (Scheme.Opens.ι_preimage_self _), ← one_eq_top, one_mul]

/-- A dominant morphism of integral schemes locally of finite type that identifies exceptional
curves of the first kind and induces an isomorphism on the ambient local rings at one point of
the source curve is quasi-finite along the entire curve. -/
theorem quasiFiniteAt_of_isExceptionalCurveOfFirstKind
    (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    (hI : I.IsExceptionalCurveOfFirstKind) (hJ : J.IsExceptionalCurveOfFirstKind)
    (g : I.subscheme ⟶ J.subscheme) [IsIso g]
    (w : I.subschemeι ≫ f = g ≫ J.subschemeι)
    (z₀ : I.subscheme) [IsIso (f.stalkMap (I.subschemeι z₀))]
    (z : I.subscheme) : f.QuasiFiniteAt (I.subschemeι z) := by
  obtain ⟨U, hIU, heq⟩ := f.exists_comap_eq_on_open_of_isExceptionalCurveOfFirstKind hI hJ g w z₀
  rw [quasiFiniteAt_iff_isOpen_singleton_asFiber]
  let y := f (I.subschemeι z)
  have hy : y ∈ (J.support : Set Y) := by
    rw [← range_subschemeι]
    exact ⟨g z, congr($(w) z).symm⟩
  have heq' : U.ι ⁻¹' (f ⁻¹' (J.support : Set Y)) = U.ι ⁻¹' (I.support : Set X) := by
    simpa only [support_comap, Closeds.coe_preimage] using
      congrArg (fun K : (U : Scheme).IdealSheafData ↦ (K.support : Set U)) heq
  have hs : {f.asFiber (I.subschemeι z)} = f.fiberι y ⁻¹' (U : Set X) := by
    symm
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · have hz : I.subschemeι z ∈ (I.support : Set X) :=
        I.range_subschemeι ▸ Set.mem_range_self z
      simpa only [y, Set.mem_preimage, fiberι_asFiber] using hIU hz
    · intro a ha
      have haFiber : f.fiberι y a ∈ Set.range (f.fiberι y) := Set.mem_range_self a
      rw [f.range_fiberι y] at haFiber
      have haf : f (f.fiberι y a) = y := Set.mem_singleton_iff.mp (Set.mem_preimage.mp haFiber)
      let aU : U := ⟨f.fiberι y a, ha⟩
      have hmem : aU ∈ U.ι ⁻¹' (f ⁻¹' (J.support : Set Y)) := by
        -- Evaluate the open immersion on the point viewed in the open subscheme.
        change f (f.fiberι y a) ∈ J.support
        rwa [haf]
      rw [heq'] at hmem
      have haI : f.fiberι y a ∈ (I.support : Set X) := hmem
      rw [← range_subschemeι] at haI
      obtain ⟨b, hb⟩ := haI
      have hbz : b = z := by
        apply g.isEmbedding.injective
        apply J.subschemeι.isEmbedding.injective
        calc
          J.subschemeι (g b) = f (I.subschemeι b) := congr($(w) b).symm
          _ = f (I.subschemeι z) := (congrArg f hb).trans haf
          _ = J.subschemeι (g z) := congr($(w) z)
      apply (f.fiberι y).isEmbedding.injective
      rw [fiberι_asFiber, ← hb, hbz]
  rw [hs]
  exact U.isOpen.preimage (f.fiberι y).continuous

end AlgebraicGeometry.Scheme.Hom
