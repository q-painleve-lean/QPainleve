/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Finite
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Basic
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Lifting a contraction of an exceptional curve to a blowup

If the inverse image of the center is an exceptional curve of the first kind, a
proper morphism that is an isomorphism off the center lifts finitely to the blowup.
The degree-one conormal prevents the lift from contracting the exceptional curve
again. For a modification, normality of the blowup then gives an isomorphism.

See [Stacks Project, Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

open LineBundleClass

variable {X Y : Scheme.{u}} {E : X.IdealSheafData} {I : Y.IdealSheafData}

private theorem not_subsingleton_range_blowupLift (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) (hI : I.comap f = E)
    (H : (I.comap f).IsEffectiveCartier) [IsProper (I.blowupLift f H)] :
    ¬ (Set.range (E.subschemeι ≫ I.blowupLift f H)).Subsingleton := by
  let g := I.blowupLift f H
  let r := E.subschemeι ≫ g
  have : IsProper r := inferInstanceAs (IsProper (E.subschemeι ≫ g))
  intro hr
  have := hE.isIntegral_subscheme
  let z := r.toImage (genericPoint E.subscheme)
  have himage : Set.range r.imageι = Set.range r := r.range_imageι.trans
    (r.isClosedMap.isClosed_range.closure_eq)
  have hspec (x : r.image) : x ⤳ z := by
    have hEq : x = z := r.imageι.injective
      (hr (himage ▸ Set.mem_range_self x) (himage ▸ Set.mem_range_self z))
    rw [hEq]
  -- The pullback of the blowup ideal is the exceptional curve ideal.
  let F := I.comap I.blowupToBase
  let hF := I.isEffectiveCartier_comap_blowupToBase
  have hc : F.comap g = E := (I.comap_blowupLift_exceptional f H).trans hI
  have hp : pullback g (LineBundleClass.mk hF.toInvertibleSheaf) =
      LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf :=
    (hF.pullback_mk_toInvertibleSheaf (hc.symm ▸ hE.isEffectiveCartier)).trans
      (mk_toInvertibleSheaf_congr _ _ hc)
  have ht : pullback r (LineBundleClass.mk hF.toInvertibleSheaf) = 1 := by
    rw [← r.toImage_imageι, ← pullback_comp,
      eq_one_of_forall_specializes hspec
        (pullback r.imageι (LineBundleClass.mk hF.toInvertibleSheaf)), pullback_one]
  obtain ⟨κ, _, e, he⟩ := hE.exists_iso
  have hd : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) = 1 := by
    rw [intersectionNumber_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he
  rw [← hp, intersectionNumber_pullback, Category.assoc, ← intersectionNumber_pullback,
    intersectionNumber_def, ht, pullback_one, eulerDegree_one] at hd
  exact zero_ne_one hd

/-- A proper morphism that is an isomorphism off the blowup center lifts finitely
when the inverse image ideal defines an exceptional curve of the first kind. -/
theorem isFinite_blowupLift_of_exceptional_contraction (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hI : I.comap f = E) (hU : I.support.compl ≤ f.isoLocus) :
    IsFinite (I.blowupLift f (hI.symm ▸ hE.isEffectiveCartier)) := by
  let H : (I.comap f).IsEffectiveCartier := hI.symm ▸ hE.isEffectiveCartier
  let g := I.blowupLift f H
  have hcomp : g ≫ I.blowupToBase = f := I.blowupLift_blowupToBase f H
  have : IsProper (g ≫ I.blowupToBase) := hcomp.symm ▸ ‹IsProper f›
  have : IsProper g := IsProper.of_comp g I.blowupToBase
  have : CompactSpace I.blowup := QuasiCompact.compactSpace_of_compactSpace I.blowupToBase
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian E.subscheme := LocallyOfFiniteType.isLocallyNoetherian E.subschemeι
  have : CompactSpace E.subscheme := hE.compactSpace
  have : IsNoetherian E.subscheme := ⟨⟩
  have := hE.isIntegral_subscheme
  refine g.isFinite_iff_forall_isClosed_finite_preimage_singleton.mpr fun y hy ↦ ?_
  have hpoint (x : X) : I.blowupToBase (g x) = f x :=
    congrArg (fun u : X ⟶ Y ↦ u x) hcomp
  by_cases hyI : I.blowupToBase y ∈ I.support.compl
  · apply Set.Subsingleton.finite
    intro x hx x' hx'
    have hbase (a : X) (ha : a ∈ g ⁻¹' {y}) : f a = I.blowupToBase y :=
      (hpoint a).symm.trans (congrArg I.blowupToBase (Set.mem_singleton_iff.mp ha))
    have hx₀ := hbase x hx
    have hx₁ := hbase x' hx'
    exact f.injOn_preimage_isoLocus (hU (hx₀.symm ▸ hyI)) (hU (hx₁.symm ▸ hyI))
      (hx₀.trans hx₁.symm)
  · -- A closed fiber containing the generic point of the exceptional curve
    -- would contract the entire curve.
    let r := E.subschemeι ≫ g
    have hz : genericPoint E.subscheme ∉ r ⁻¹' {y} := by
      intro hη
      have hall : Set.univ ⊆ r ⁻¹' {y} := by
        rw [← genericPoint_spec E.subscheme]
        exact closure_minimal (Set.singleton_subset_iff.mpr hη) (hy.preimage r.continuous)
      apply hE.not_subsingleton_range_blowupLift f hI H
      exact Set.subsingleton_singleton.anti
        (Set.range_subset_iff.mpr fun x ↦ hall (Set.mem_univ x))
    have hfin := Scheme.finite_of_isClosed_of_genericPoint_notMem
      hE.topologicalKrullDim_subscheme.le (hy.preimage r.continuous) hz
    refine (hfin.image E.subschemeι).subset fun x hx ↦ ?_
    have hxE : x ∈ (E.support : Set X) := by
      rw [← hI, support_comap, Closeds.coe_preimage, Set.mem_preimage,
        ← hpoint, Set.mem_singleton_iff.mp hx]
      exact not_not.mp hyI
    obtain ⟨z, rfl⟩ := E.range_subschemeι.symm ▸ hxE
    exact ⟨z, hx, rfl⟩

/-- The canonical finite lift of a modification contracting an exceptional curve of the
first kind is an isomorphism when the target blowup is normal. -/
theorem isIso_blowupLift_of_exceptional_contraction [IsReduced X] [IsIntegral Y]
    [IsNoetherian Y] [IsNormalScheme I.blowup] (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsModification f] (hI : I.comap f = E) (hU : I.support.compl ≤ f.isoLocus) :
    IsIso (I.blowupLift f (hI.symm ▸ hE.isEffectiveCartier)) := by
  let H : (I.comap f).IsEffectiveCartier := hI.symm ▸ hE.isEffectiveCartier
  let g := I.blowupLift f H
  have := (IsModification.birational f).irreducibleSpace
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hx : genericPoint X ∉ (E.support : Set X) :=
    hE.isEffectiveCartier.genericPoint_notMem_support
  have hy : f (genericPoint X) ∈ I.support.compl := by
    apply f.mem_preimage.mp
    rw [← I.compl_support_comap f, hI]
    exact hx
  have hne : Nonempty I.support.compl := ⟨⟨_, hy⟩⟩
  have hD : Dense (I.support.compl : Set Y) :=
    I.support.compl.isOpen.dense ⟨_, hy⟩
  have : IsIntegral I.blowup := I.isIntegral_blowup_of_nonempty_compl_support hne
  have : IsModification I.blowupToBase := I.isModification_blowupToBase hD
  have : IsModification (g ≫ I.blowupToBase) :=
    (I.blowupLift_blowupToBase f H).symm ▸ inferInstanceAs (IsModification f)
  have : IsModification g := IsModification.of_comp_right g I.blowupToBase
  have : IsFinite g := hE.isFinite_blowupLift_of_exceptional_contraction f hI hU
  exact IsModification.isIso_of_isFinite g

/-- A modification of a Noetherian integral scheme from a regular scheme is the blowup of a
closed point of local dimension two if its centre is that point, the point is regular, and its
scheme-theoretic fiber is an exceptional curve of the first kind. -/
theorem isIso_blowupLift_of_regular_contraction_point [IsRegular X] [IsIntegral Y] [IsNoetherian Y]
    {p : Y} [IsRegularLocalRing (Y.presheaf.stalk p)]
    (hE : E.IsExceptionalCurveOfFirstKind) (f : X ⟶ Y) [IsModification f]
    (hc : f.centre = {p}) (hdim : ringKrullDim (Y.presheaf.stalk p) = 2)
    (hI : (Y.fromSpecResidueField p).ker.comap f = E) :
    IsIso ((Y.fromSpecResidueField p).ker.blowupLift f (hI.symm ▸ hE.isEffectiveCartier)) := by
  have hp : IsClosed ({p} : Set Y) := hc ▸ f.isClosed_centre
  have hmem (y : Y) : y ∈ (Y.fromSpecResidueField p).ker.support.compl ↔ y ≠ p := by
    rw [← SetLike.mem_coe, Closeds.coe_compl,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp, Set.mem_compl_iff,
      Set.mem_singleton_iff]
  have hU : (Y.fromSpecResidueField p).ker.support.compl ≤ f.isoLocus := by
    intro y hy
    have hy' : y ∉ ({p} : Set Y) := fun h ↦ (hmem y).mp hy (Set.mem_singleton_iff.mp h)
    simpa only [← SetLike.mem_coe, ← hc, Scheme.Hom.centre_def,
      Set.mem_compl_iff, not_not] using hy'
  have : IsRegular Y := f.isRegular_of_isRegularLocalRing_of_mem_centre fun y hy ↦ by
    rw [hc, Set.mem_singleton_iff] at hy
    subst y
    infer_instance
  have : IsRegular (Y.fromSpecResidueField p).ker.blowup :=
    Y.ker_fromSpecResidueField_eq_vanishingIdeal p ▸ isRegular_blowup_closed_point hdim hp
  exact hE.isIso_blowupLift_of_exceptional_contraction f hI hU

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
