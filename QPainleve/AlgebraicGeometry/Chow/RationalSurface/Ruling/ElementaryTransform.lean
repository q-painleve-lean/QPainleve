/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import QPainleve.AlgebraicGeometry.Curves.GenusZero
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Nodality
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.RegularCurve
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Reduced
import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Descent.Contraction
import TauCeti.AlgebraicGeometry.Morphisms.Epi
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Elementary transformations at boundary nodes

Blowing up a node on a projective-line fiber and contracting the strict transform of
the fiber replaces that fiber by a component of the anticanonical boundary. If the
original fiber is not a boundary component, the contraction is internal and the
reduced total boundary descends isomorphically.

This is the elementary transformation in [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TauCeti.AlgebraicGeometry LineBundleClass

namespace AlgebraicGeometry.Scheme.Hom

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X C : Scheme.{u}} [X.Over (Spec (.of k))] [C.Over (Spec (.of k))]
  [IsIntegral X] [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

open Scheme.IdealSheafData

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" Y "]" => LineBundleClass.mk (QPainleve.canonicalBundle k Y 2)
local notation "J[" x "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField _ x)
local notation "I[" p "]" => vanishingIdeal (Closeds.mk (closure ({p} : Set X)) isClosed_closure)
local notation "π[" p "]" => blowupToBase (I[p])
local notation "E[" p "]" => comap (I[p]) (π[p])
local notation "B[" p "]" => blowup (I[p])
local notation "F[" f "," y "]" => comap (J[y]) f
local notation "F₁[" p "," f "," y "]" => Scheme.Hom.ker (blowupMap (I[p]) (subschemeι (F[f,y])))

omit [IsAlgClosed k] [X.Over S] [C.Over S] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem exists_iso_strictTransform_fiber
    (f : X ⟶ C) {p : X} (hp : IsClosed ({p} : Set X)) {y : C}
    (a : (F[f,y]).subscheme ≅ projectiveLine k) :
    ∃ e : (F₁[p,f,y]).subscheme ≅ (F[f,y]).subscheme,
      e.hom ≫ (F[f,y]).subschemeι = (F₁[p,f,y]).subschemeι ≫ π[p] := by
  have : IrreducibleSpace (F[f,y]).subscheme :=
    a.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  have : TauCeti.AlgebraicGeometry.IsRegular (projectiveLine k) := ⟨fun _ ↦ inferInstance⟩
  have : TauCeti.AlgebraicGeometry.IsRegular (F[f,y]).subscheme :=
    IsRegular.of_isOpenImmersion a.hom
  have hd := a.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)
  have h := (F[f,y]).exists_iso_strictTransform_of_regularCurve hd hp
  dsimp only at h
  rwa [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal] at h

omit [C.Over S] in
private theorem fiber_self_intersection
    (f : X ⟶ C) {y : C} (hy : IsClosed ({y} : Set C))
    (hJ : (J[y]).IsEffectiveCartier) (hF : (F[f,y]).IsEffectiveCartier)
    (a : (F[f,y]).subscheme ≅ projectiveLine k) :
    let L := (LineBundleClass.mk hF.toInvertibleSheaf)⁻¹
    Chow.classIntersectionNumber k X L L = 0 := by
  intro L
  let j := C.fromSpecResidueField y
  let : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hy
  let b := subschemeMap (F[f,y]) (J[y]) f ((J[y]).le_map_comap f) ≫ inv j.toImage
  have hb : b ≫ j = (F[f,y]).subschemeι ≫ f := by
    rw [← j.toImage_imageι, Category.assoc, IsIso.inv_hom_id_assoc]
    exact subschemeMap_subschemeι ..
  have hd := a.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Nonempty (F[f,y]).subscheme := a.hom.homeomorph.nonempty_congr.mpr inferInstance
  have : IsIntegral (F[f,y]).subscheme := isIntegral_of_isOpenImmersion a.hom
  rw [Chow.classIntersectionNumber_eq_intersectionNumber_subschemeι k hX.le hF hd]
  have hL : L = pullback f (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ := by
    rw [pullback_inv, hJ.pullback_mk_toInvertibleSheaf hF]
  rw [hL, intersectionNumber_pullback]
  exact intersectionNumber_eq_zero_of_eq_comp k _ b j hb.symm
    (t := IsLocalRing.closedPoint (C.residueField y))
    (fun z ↦ specializes_of_eq (Subsingleton.elim z _)) _

omit [IsAlgClosed k] [C.Over S] [IsIntegral X] [X.IsProjectiveOver k] in
private theorem fiber_stalkOrder_eq_one
    (f : X ⟶ C) {p : X} {y : C} (hpy : f p = y)
    (hy : IsClosed ({y} : Set C)) (hF : (F[f,y]).IsEffectiveCartier)
    (a : (F[f,y]).subscheme ≅ projectiveLine k) :
    (F[f,y]).stalkOrder p = 1 := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have hmem : p ∈ ((F[f,y]).support : Set X) := by
    rw [support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hy, Set.mem_preimage, hpy]
    exact Set.mem_singleton y
  obtain ⟨z, hz⟩ := (F[f,y]).range_subschemeι.symm ▸ hmem
  have : TauCeti.AlgebraicGeometry.IsRegular (projectiveLine k) := ⟨fun _ ↦ inferInstance⟩
  have : TauCeti.AlgebraicGeometry.IsRegular (F[f,y]).subscheme :=
    IsRegular.of_isOpenImmersion a.hom
  have := isRegularLocalRing_stalk_of_smooth (X ↘ S) ((F[f,y]).subschemeι z)
  rw [← hz]
  exact (hF.stalkOrder_eq_one_iff_isRegularLocalRing z).mpr inferInstance

omit [C.Over S] in
private theorem strictTransform_fiber_isExceptionalCurveOfFirstKind
    (f : X ⟶ C) {p : X} (hp : IsClosed ({p} : Set X)) {y : C} (hpy : f p = y)
    (hy : IsClosed ({y} : Set C)) (hJ : (J[y]).IsEffectiveCartier)
    (hF : (F[f,y]).IsEffectiveCartier) (a : (F[f,y]).subscheme ≅ projectiveLine k)
    (ha : a.hom.IsOver S) :
    (F₁[p,f,y]).IsExceptionalCurveOfFirstKind := by
  let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
  have : B[p].IsProjectiveOver k := (I[p]).isProjectiveOver_blowup_of_isNoetherianRing k
  have hSmooth : SmoothOfRelativeDimension 2 (B[p] ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
  obtain ⟨e, he⟩ := f.exists_iso_strictTransform_fiber hp a
  have : e.hom.IsOver S := ⟨by
    rw [IdealSheafData.over_eq_subschemeι_comp, IdealSheafData.over_eq_subschemeι_comp,
      ← Category.assoc, he, Category.assoc]
    rfl⟩
  let d := e ≪≫ a
  have : d.hom.IsOver S := inferInstanceAs ((e.hom ≫ a.hom).IsOver S)
  have : Nonempty (F₁[p,f,y]).subscheme := d.hom.homeomorph.nonempty_congr.mpr inferInstance
  have : IsIntegral (F₁[p,f,y]).subscheme := isIntegral_of_isOpenImmersion d.hom
  have : (F₁[p,f,y]).subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstanceAs (IsProper ((F₁[p,f,y]).subschemeι ≫ B[p] ↘ S)),
      d.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans
        (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k)⟩
  have : IsIntegral B[p] := isIntegral_blowup_closed_point (X ↘ S) hp
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (B[p] ↘ S) (n := 2)
  have hs := Chow.classIntersectionNumber_self_strictTransform_pointBlowup p k hp hF
  dsimp only at hs
  rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal] at hs
  obtain ⟨hF', hs⟩ := hs
  have hm := f.fiber_stalkOrder_eq_one hpy hy hF a
  exact (hF'.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber hX.le).mpr
    ⟨Scheme.genus_eq_zero_iff_exists_iso_projectiveLine.mpr ⟨d, inferInstance⟩,
      by simpa only [f.fiber_self_intersection hy hJ hF a, hm, ENat.toNat_one,
        Nat.cast_one, one_pow, zero_sub] using hs⟩

local notation "R[" p "," D "]" => radical (comap D (π[p]))

omit [IsAlgClosed k] [X.Over S] [C.Over S] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem strictTransform_fiber_not_le_boundary
    (f : X ⟶ C) {p : X} (hp : IsClosed ({p} : Set X)) {y : C}
    (a : (F[f,y]).subscheme ≅ projectiveLine k) {D : X.IdealSheafData}
    (hF : ¬ (F[f,y]).support ≤ D.support) :
    ¬ (F₁[p,f,y]).support ≤ (R[p,D]).support := by
  obtain ⟨e, he⟩ := f.exists_iso_strictTransform_fiber hp a
  intro h
  apply hF
  intro x hx
  have hx' : x ∈ Set.range (F[f,y]).subschemeι := (F[f,y]).range_subschemeι.symm ▸ hx
  obtain ⟨z, rfl⟩ := hx'
  obtain ⟨w, rfl⟩ := e.hom.surjective z
  have hw : (F₁[p,f,y]).subschemeι w ∈ ((F₁[p,f,y]).support : Set B[p]) :=
    (F₁[p,f,y]).range_subschemeι ▸ Set.mem_range_self w
  have hz : (F₁[p,f,y]).subschemeι w ∈ ((R[p,D]).support : Set B[p]) := h hw
  rw [support_radical, support_comap, Closeds.coe_preimage, Set.mem_preimage] at hz
  have hew := congrArg (fun h : _ ⟶ X ↦ h w) he
  simp only [Scheme.Hom.comp_apply] at hew
  rwa [hew]

omit [IsAlgClosed k] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem exists_descended_ruling
    (f : X ⟶ C) [f.IsOver S] {p : X} (hp : IsClosed ({p} : Set X))
    {y : C} (hy : IsClosed ({y} : Set C)) {Y : Scheme.{u}} [Y.Over S]
    (g : B[p] ⟶ Y) [IsModification g] {q : Y}
    (hc : g.centre = {q}) (hgF : (J[q]).comap g = F₁[p,f,y])
    (hq : IsClosed ({q} : Set Y)) (a : (F[f,y]).subscheme ≅ projectiveLine k)
    (hΓ : ∀ U : Y.Opens, IsIso (g.app U)) :
    let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
    g.IsOver S → ∃ f' : Y ⟶ C, f'.IsOver S ∧ g ≫ f' = π[p] ≫ f ∧ f' q = y := by
  intro hOver hg
  let := hOver
  obtain ⟨e, he⟩ := f.exists_iso_strictTransform_fiber hp a
  have hpre : ∀ {x : B[p]}, g x = q → (π[p] ≫ f) x = y := by
    intro x hx
    have hx' : x ∈ ((F₁[p,f,y]).support : Set B[p]) := by
      rw [← hgF, support_comap, Closeds.coe_preimage,
        Scheme.support_ker_fromSpecResidueField_of_isClosed hq, Set.mem_preimage, hx]
      exact Set.mem_singleton q
    obtain ⟨w, rfl⟩ := (F₁[p,f,y]).range_subschemeι.symm ▸ hx'
    have hw : (F[f,y]).subschemeι (e.hom w) ∈ ((F[f,y]).support : Set X) :=
      (F[f,y]).range_subschemeι ▸ Set.mem_range_self (e.hom w)
    rw [support_comap, Closeds.coe_preimage, Scheme.support_ker_fromSpecResidueField_of_isClosed hy,
      Set.mem_preimage, Set.mem_singleton_iff] at hw
    have hew := congrArg (fun h : _ ⟶ X ↦ h w) he
    simp only [Scheme.Hom.comp_apply] at hew
    simpa only [Scheme.Hom.comp_apply, hew] using hw
  have hconst : Function.FactorsThrough (π[p] ≫ f) g := by
    intro x z hxz
    by_cases hx : g x = q
    · exact (hpre hx).trans (hpre (hxz.symm.trans hx)).symm
    · have hmem {w : B[p]} (hw : g w ≠ q) : g w ∈ g.isoLocus := by
        rw [← SetLike.mem_coe, ← Scheme.Hom.compl_centre, hc, Set.mem_compl_iff,
          Set.mem_singleton_iff]
        exact hw
      exact congrArg (π[p] ≫ f) (g.injOn_preimage_isoLocus (hmem hx) (hmem (hxz ▸ hx)) hxz)
  obtain ⟨f', hf', -⟩ := g.existsUnique_comp_eq_of_universallyClosed hΓ _ hconst
  have hEpi := g.epi_of_surjective_of_app_injective fun U ↦ by
    have := hΓ U
    exact (ConcreteCategory.bijective_of_isIso (g.app U)).1
  refine ⟨f', ⟨(cancel_epi g).mp ?_⟩, hf', ?_⟩
  · rw [← Category.assoc, hf', Category.assoc, comp_over f, comp_over g]
    rfl
  · obtain ⟨x, hx⟩ := g.surjective q
    rw [← hx, ← Scheme.Hom.comp_apply, hf']
    exact hpre hx

omit [IsAlgClosed k] [X.Over S] [C.Over S] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem exceptional_image_le_strictTransform_fiber_image
    (f : X ⟶ C) {p : X} (hp : IsClosed ({p} : Set X)) {y : C} (hy : IsClosed ({y} : Set C))
    (hpy : f p = y) (a : (F[f,y]).subscheme ≅ projectiveLine k)
    {Y : Scheme.{u}} (g : B[p] ⟶ Y) {q : Y} (hq : IsClosed ({q} : Set Y))
    (hgF : (J[q]).comap g = F₁[p,f,y]) (hExc : (F₁[p,f,y]).IsExceptionalCurveOfFirstKind) :
    (E[p]).map g ≤ (F₁[p,f,y]).map g := by
  obtain ⟨e, he⟩ := f.exists_iso_strictTransform_fiber hp a
  have hmem : p ∈ Set.range (F[f,y]).subschemeι := by
    rw [(F[f,y]).range_subschemeι, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hy, Set.mem_preimage, hpy]
    exact Set.mem_singleton y
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨w, hwz⟩ := e.hom.surjective z
  let x := (F₁[p,f,y]).subschemeι w
  have hπ : π[p] x = p := by
    have hw := congrArg (fun h : _ ⟶ X ↦ h w) he
    simp only [Scheme.Hom.comp_apply, x, hwz] at hw ⊢
    exact hw.symm.trans hz
  have hsupport : ((F₁[p,f,y]).support : Set B[p]) = g ⁻¹' {q} := by
    rw [← hgF, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hq]
  have hx : g x = q := by
    have hw : x ∈ Set.range (F₁[p,f,y]).subschemeι := Set.mem_range_self w
    rwa [(F₁[p,f,y]).range_subschemeι, hsupport, Set.mem_preimage, Set.mem_singleton_iff] at hw
  have hxE : x ∈ Set.range (E[p]).subschemeι := by
    rw [(E[p]).range_subschemeι, support_comap, Closeds.coe_preimage,
      coe_support_vanishingIdeal, Closeds.coe_mk, Set.mem_preimage, hπ]
    exact subset_closure (Set.mem_singleton p)
  obtain ⟨v, hv⟩ := hxE
  have hqmem : q ∈ (((E[p]).map g).support : Set Y) := by
    apply Scheme.Hom.range_subset_ker_support ((E[p]).subschemeι ≫ g)
    exact ⟨v, by rw [Scheme.Hom.comp_apply, hv, hx]⟩
  have : IsReduced (F₁[p,f,y]).subscheme := @isReduced_of_isIntegral _ hExc.isIntegral_subscheme
  have hImage : g '' ((F₁[p,f,y]).support : Set B[p]) = {q} := by
    rw [hsupport]
    exact Set.image_preimage_eq_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨x, hx⟩)
  rw [← (F₁[p,f,y]).isReduced_subscheme_iff_radical_eq.mp inferInstance,
    ← vanishingIdeal_support, map_vanishingIdeal, hImage, ← le_support_iff_le_vanishingIdeal]
  apply SetLike.coe_subset_coe.mp
  exact closure_minimal (Set.singleton_subset_iff.mpr hqmem) (((E[p]).map g).support.isClosed)

omit [IsAlgClosed k] [C.Over S] in
private theorem exists_iso_exceptional_transformed_fiber
    (f : X ⟶ C) [IsIntegral C] [IsDominant f]
    {p : X} (hp : IsClosed ({p} : Set X)) {y : C} (hy : IsClosed ({y} : Set C))
    (hpy : f p = y) (hJ : (J[y]).IsEffectiveCartier)
    (a : (F[f,y]).subscheme ≅ projectiveLine k)
    {Y : Scheme.{u}} [Y.Over S] [IsIntegral Y] [IsNoetherian Y]
    [SmoothOfRelativeDimension 2 (Y ↘ S)]
    (g : B[p] ⟶ Y) [IsModification g] (f' : Y ⟶ C)
    (hcomp : g ≫ f' = π[p] ≫ f) {q : Y} (hq : IsClosed ({q} : Set Y))
    (hgF : (J[q]).comap g = F₁[p,f,y]) (hExc : (F₁[p,f,y]).IsExceptionalCurveOfFirstKind)
    (hEmb : IsClosedImmersion ((E[p]).subschemeι ≫ g)) :
    IsDominant f' ∧ (E[p]).map g = F[f',y] ∧
      ∃ v : (E[p]).subscheme ≅ (F[f',y]).subscheme,
        v.hom ≫ (F[f',y]).subschemeι = (E[p]).subschemeι ≫ g := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have := isRegularLocalRing_stalk_of_smooth (X ↘ S) p
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ S) 2).mp
    inferInstance).2 p hp
  have : Surjective π[p] := surjective_blowupToBase_point hp hd
  have : IsDominant (g ≫ f') := hcomp.symm ▸ inferInstanceAs (IsDominant (π[p] ≫ f))
  have hd' := IsDominant.of_comp g f'
  have hF := hJ.comap_of_isDominant f
  have hF' := hJ.comap_of_isDominant f'
  have hm := f.fiber_stalkOrder_eq_one hpy hy hF a
  have htotal : (F[f',y]).comap g = F₁[p,f,y] ⊓ E[p] := by
    rw [← comap_comp, hcomp, comap_comp, inf_ker_blowupMap_subschemeι_exceptional]
    simpa only [hm, ENat.toNat_one, pow_one] using
      hF.totalTransform_eq_strictTransform_mul_pow_closedPoint hp hd
  have : IsIntegral (E[p]).subscheme := isIntegral_exceptional_blowup_closed_point hd hp
  have hEdim := (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd)
    |>.topologicalKrullDim_subscheme
  rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal] at hEdim
  have : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular Y := IsRegular.of_smooth (Y ↘ S)
  have hdimY := topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ S) (n := 2)
  have hImg : ((E[p]).map g).IsEffectiveCartier :=
    ((E[p]).subschemeι ≫ g).isEffectiveCartier_ker_of_isRegular_of_dim_eq_two k hdimY hEdim
  have : IsIntegral B[p] := isIntegral_blowup_closed_point (X ↘ S) hp
  have hEq : (E[p]).map g = F[f',y] := by
    refine le_antisymm ?_ ((le_map_iff_comap_le).mpr (htotal.trans_le inf_le_right))
    apply (hImg.comap_le_comap_iff_of_isModification g hF').mp
    rw [htotal]
    refine le_inf ?_ (comap_map_le _ _)
    exact (le_map_iff_comap_le).mp
      (exceptional_image_le_strictTransform_fiber_image f hp hy hpy a g hq hgF hExc)
  obtain ⟨v, hv⟩ := (F[f',y]).exists_iso_of_comap_eq_ker (Iso.refl Y)
    ((E[p]).subschemeι ≫ g)
    (by simpa only [Iso.refl_hom, comap_id, IdealSheafData.map] using hEq.symm)
  exact ⟨hd', hEq, v, by simpa only [Iso.refl_hom, Category.comp_id] using hv⟩

omit [IsAlgClosed k] [C.Over S] [IsIntegral X] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem exists_iso_fiber_away_from_elementary_transform
    (f : X ⟶ C) {p : X} (hp : IsClosed ({p} : Set X))
    {Y : Scheme.{u}} [Y.Over S] (g : B[p] ⟶ Y) (f' : Y ⟶ C)
    (hcomp : g ≫ f' = π[p] ≫ f)
    (hg : g ≫ Y ↘ S = π[p] ≫ X ↘ S)
    {q : Y} (hc : g.centre = {q}) {y : C} (hpy : f p = y) (hy : f' q = y)
    (hq : IsClosed ({q} : Set Y)) (hgF : (J[q]).comap g = F₁[p,f,y])
    {D : X.IdealSheafData} {D' : Y.IdealSheafData}
    (hD : D.comap (π[p]) = R[p,D] * E[p])
    (hD' : D'.comap g = R[p,D] * F₁[p,f,y])
    {z : C} (hz : IsClosed ({z} : Set C)) (hne : z ≠ y) :
    ∃ e : (F[f',z]).subscheme ≅ (F[f,z]).subscheme, e.hom.IsOver S ∧
      D.comap (e.hom ≫ (F[f,z]).subschemeι) = D'.comap (F[f',z]).subschemeι := by
  have hπ : Set.range (F[f,z]).subschemeι ⊆ (I[p]).support.compl := by
    rw [(F[f,z]).range_subschemeι, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hz]
    rw [Closeds.coe_compl, coe_support_vanishingIdeal, Closeds.coe_mk, hp.closure_eq]
    exact fun x hx he ↦ hne ((Set.mem_singleton_iff.mp hx).symm.trans
      ((congrArg f (Set.mem_singleton_iff.mp he)).trans hpy))
  have hq' : ((J[q]).support : Set Y) = {q} :=
    Scheme.support_ker_fromSpecResidueField_of_isClosed hq
  have hAway : Set.range (F[f',z]).subschemeι ⊆ (J[q]).support.compl := by
    rw [Closeds.coe_compl, hq', (F[f',z]).range_subschemeι, support_comap,
      Closeds.coe_preimage, Scheme.support_ker_fromSpecResidueField_of_isClosed hz]
    exact fun x hx he ↦ hne ((Set.mem_singleton_iff.mp hx).symm.trans
      ((congrArg f' (Set.mem_singleton_iff.mp he)).trans hy))
  have hIso : ((J[q]).support.compl : Set Y) ⊆ g.isoLocus := by
    rw [Closeds.coe_compl, hq', ← Scheme.Hom.compl_centre, hc]
  obtain ⟨j, hj⟩ := (π[p]).exists_isPullback_id_of_range_subset_isoLocus (F[f,z]).subschemeι
    (hπ.trans ((π[p]).le_isoLocus_iff.mpr (I[p]).isIso_blowupToBase_restrict_compl_support))
  obtain ⟨j', hj'⟩ := g.exists_isPullback_id_of_range_subset_isoLocus (F[f',z]).subschemeι
    (hAway.trans hIso)
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hj.flip inferInstance
  have : IsClosedImmersion j' := MorphismProperty.of_isPullback hj'.flip inferInstance
  have hk : j.ker = j'.ker := by
    rw [ker_eq_comap_of_isPullback _ hj, ker_eq_comap_of_isPullback _ hj', ker_subschemeι,
      ker_subschemeι, ← comap_comp, ← comap_comp, hcomp]
  let u := IsClosedImmersion.lift j j' hk.le
  have hu : u ≫ j = j' := IsClosedImmersion.lift_fac _ _ _
  have : IsIso u := IsClosedImmersion.isIso_lift _ _ hk
  have h₁ : j ≫ π[p] = (F[f,z]).subschemeι := by simpa only [Category.id_comp] using hj.w
  have h₂ : j' ≫ g = (F[f',z]).subschemeι := by simpa only [Category.id_comp] using hj'.w
  have h₃ : u ≫ (F[f,z]).subschemeι = j' ≫ π[p] := by rw [← h₁, ← Category.assoc, hu]
  have hE : (E[p]).comap j' = ⊤ := by
    rw [← comap_comp, ← h₃, comap_eq_top_iff, ← top_le_iff]
    exact fun x _ ↦ hπ ⟨u x, Scheme.Hom.comp_apply _ _ _ |>.symm⟩
  have hF : (F₁[p,f,y]).comap j' = ⊤ := by
    rw [← hgF, ← comap_comp, h₂, comap_eq_top_iff, ← top_le_iff]
    exact fun x _ ↦ hAway (Set.mem_range_self x)
  refine ⟨asIso u, ⟨?_⟩, ?_⟩
  · rw [asIso_hom, IdealSheafData.over_eq_subschemeι_comp,
      IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc, h₃, ← h₂,
      Category.assoc, Category.assoc, hg]
  · rw [asIso_hom, h₃, ← h₂, comap_comp D, comap_comp D', hD, hD',
      comap_mul, comap_mul, hE, hF, mul_top]

/-- At a boundary node on a projective-line fiber that is not a boundary component,
the strict transform of the fiber contracts after blowing up the node. The reduced
total boundary omits the contracted strict transform and descends isomorphically to
a nodal anticanonical boundary. The ruling
descends over the same base, with a new boundary component as the scheme-theoretic
fiber over the chosen point. The other closed fibers keep their boundary restrictions. -/
theorem exists_elementary_transform_of_nodal_fiber
    (f : X ⟶ C) [f.IsOver S] [IsIntegral C] [IsDominant f]
    {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hK : LineBundleClass.mk hD.toInvertibleSheaf = K[X])
    {p : X} (hp : IsClosed ({p} : Set X)) (hn : D.IsNodeOfReducedBoundary (X ↘ S) p)
    {y : C} (hy : IsClosed ({y} : Set C)) (hpy : f p = y)
    (hJ : (J[y]).IsEffectiveCartier)
    (a : (F[f,y]).subscheme ≅ projectiveLine k) (ha : a.hom.IsOver S)
    (hF : ¬ (F[f,y]).support ≤ D.support) :
    let : B[p].Over S := ⟨π[p] ≫ X ↘ S⟩
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S) (g : B[p] ⟶ Y) (q : Y) (f' : Y ⟶ C),
      let : Y.Over S := ⟨s⟩
      ∃ hSmooth : SmoothOfRelativeDimension 2 s,
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
      let D' := (R[p,D]).map g
      IsIntegral Y ∧ Y.IsProjectiveOver k ∧
      IsModification g ∧ g.IsOver S ∧ IsDominant f' ∧ f'.IsOver S ∧ g ≫ f' = π[p] ≫ f ∧
      IsClosed ({q} : Set Y) ∧ g.centre = {q} ∧ (J[q]).comap g = F₁[p,f,y] ∧
      ¬ ((J[q]).comap g).support ≤ (R[p,D]).support ∧
      (E[p]).map g = F[f',y] ∧ D' ≤ F[f',y] ∧ f' q = y ∧
      (∃ v : (E[p]).subscheme ≅ (F[f',y]).subscheme,
        v.hom ≫ (F[f',y]).subschemeι = (E[p]).subschemeι ≫ g) ∧
      D.comap (π[p]) = R[p,D] * E[p] ∧ D'.comap g = R[p,D] * F₁[p,f,y] ∧
      (∀ z : C, IsClosed ({z} : Set C) → z ≠ y →
        ∃ b : (F[f',z]).subscheme ≅ (F[f,z]).subscheme, b.hom.IsOver S ∧
          D.comap (b.hom ≫ (F[f,z]).subschemeι) = D'.comap (F[f',z]).subschemeι) ∧
      (∃ e : B[p] ≅ (J[q]).blowup, e.hom ≫ (J[q]).blowupToBase = g) ∧
      ∃ hD' : D'.IsEffectiveCartier,
        LineBundleClass.mk hD'.toInvertibleSheaf = K[Y] ∧
        AtWorstNodalOfRelativeDimensionOne (D'.subschemeι ≫ s) ∧
        ∃ d : (R[p,D]).subscheme ≅ D'.subscheme,
          d.hom ≫ D'.subschemeι = (R[p,D]).subschemeι ≫ g := by
  intro hOver
  let := hOver
  have : IsIntegral B[p] := isIntegral_blowup_closed_point (X ↘ S) hp
  have : B[p].IsProjectiveOver k := (I[p]).isProjectiveOver_blowup_of_isNoetherianRing k
  have hSmoothB : SmoothOfRelativeDimension 2 (B[p] ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
  have := hSmoothB.smooth
  have hFiber := hJ.comap_of_isDominant f
  have hExc := f.strictTransform_fiber_isExceptionalCurveOfFirstKind hp hpy hy hJ hFiber a ha
  obtain ⟨Y, s, g, q, hIntegral, hProj, hSmooth, hg, hmod, hq, hc, hgF, hΓ, e, he⟩ :=
    hExc.exists_smooth_projective_contraction (k := k)
  let : Y.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hSmooth
  obtain ⟨f', hf', hcomp, hfq⟩ := f.exists_descended_ruling hp hy g hc hgF hq a hΓ hg
  obtain ⟨hR, hcanR, htotal, hER, hnodalR⟩ :=
    hD.isAnticanonical_reducedTotalTransform_of_node hN hK hp hn
  have hnot := f.strictTransform_fiber_not_le_boundary hp a hF
  have : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
  let Q := vanishingIdeal (Closeds.mk (closure ({q} : Set Y)) isClosed_closure)
  have hQ : J[q] = Q := Y.ker_fromSpecResidueField_eq_vanishingIdeal q
  have hBlow : ∃ u : Q.blowup ≅ B[p], u.hom ≫ g = Q.blowupToBase := by
    rw [← hQ]
    exact ⟨e.symm, by rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩
  obtain ⟨u, hu⟩ := hBlow
  have hQF : Q.comap g = F₁[p,f,y] := hQ ▸ hgF
  obtain ⟨hD', hK', hN', -, htotal', -, -, d, hd⟩ :=
    hR.internalBlowdown_of_anticanonical_of_blowupIso k hq g u hu
      (hQF.symm ▸ hnot) hnodalR hcanR
  let j := inclusion hER
  have hj : IsClosedImmersion (j ≫ (R[p,D]).subschemeι) := by
    rw [inclusion_subschemeι]
    infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp_isClosedImmersion j (R[p,D]).subschemeι
  have hEmb : IsClosedImmersion ((E[p]).subschemeι ≫ g) := by
    rw [← inclusion_subschemeι hER, Category.assoc, ← hd]
    infer_instance
  obtain ⟨hdom, hEq, hIso⟩ :=
    f.exists_iso_exceptional_transformed_fiber hp hy hpy hJ a g f' hcomp hq hgF hExc hEmb
  refine ⟨Y, s, g, q, f', hSmooth, hIntegral, hProj, hmod, hg, hdom, hf', hcomp,
    hq, hc, hgF, hgF.symm ▸ hnot, hEq, hEq ▸ map_mono g hER, hfq, hIso,
    htotal, hQF ▸ htotal', ?_, ⟨e, he⟩, hD', hK', hN', d, hd⟩
  intro z hz hzy
  exact f.exists_iso_fiber_away_from_elementary_transform hp g f' hcomp (comp_over g S)
    hc hpy hfq hq hgF htotal (hQF ▸ htotal') hz hzy

end AlgebraicGeometry.Scheme.Hom
