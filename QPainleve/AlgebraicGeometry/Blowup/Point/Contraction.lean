/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Comparison
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Modification
import QPainleve.AlgebraicGeometry.Blowup.Point.Lift
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Contracting the source exceptional curve of a lift

Consider a commuting square of point blowups whose lower arrow is a modification.
If the source center maps to the target center and the latter belongs to the centre of the
lower modification, the upper arrow contracts the source exceptional curve and descends
to a lift on the original source.

The proof follows the exceptional-curve argument of
[The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

universe u

variable {X Y : Scheme.{u}} {p : X} {q : Y}

local notation "𝔪[" x "]" =>
  vanishingIdeal (Closeds.mk (closure (Set.singleton x)) isClosed_closure)
local notation "πₚ" => blowupToBase 𝔪[p]
local notation "π_q" => blowupToBase 𝔪[q]
local notation "Eₚ" => IdealSheafData.comap 𝔪[p] πₚ
local notation "E_q" => IdealSheafData.comap 𝔪[q] π_q

/-- In a commuting square of blowups at closed points with two-dimensional local rings on
regular schemes, let the lower map be a modification and send the source center to the target
center. If it fails to be an isomorphism at the target center, the upper map is constant on
the source exceptional fiber. -/
theorem range_exceptional_subsingleton_of_mem_centre [IsRegular X] [IsRegular Y]
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsModification f]
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Y))
    (hdp : ringKrullDim (X.presheaf.stalk p) = 2)
    (hdq : ringKrullDim (Y.presheaf.stalk q) = 2)
    (g : 𝔪[p].blowup ⟶ 𝔪[q].blowup)
    (hcomm : g ≫ π_q = πₚ ≫ f) (hpoint : f p = q) (hc : q ∈ f.centre) :
    (Set.range ((Eₚ).subschemeι ≫ g)).Subsingleton := by
  have hn : q ∉ (f.isoLocus : Set Y) := by
    simpa only [centre_def, Set.mem_compl_iff] using hc
  have hsupport : (𝔪[q].support : Set Y) = {q} :=
    (coe_support_vanishingIdeal _).trans hq.closure_eq
  have hdense : Dense (𝔪[q].support.compl : Set Y) := by
    rw [Closeds.coe_compl, hsupport]
    exact (IsModification.dense_isoLocus f).mono (Set.subset_compl_singleton_iff.mpr hn)
  have hsupport' : (𝔪[p].support : Set X) = {p} :=
    (coe_support_vanishingIdeal _).trans hp.closure_eq
  have hdense' : Dense (𝔪[p].support.compl : Set X) := by
    rw [Closeds.coe_compl, hsupport']
    apply ((inferInstance : IsModification f).dense_preimage hdense).mono
    apply Set.subset_compl_singleton_iff.mpr
    simpa only [Opens.map_coe, Closeds.coe_compl, hsupport, Set.preimage_compl,
      Set.mem_compl_iff, Set.mem_preimage, not_not, hpoint] using Set.mem_singleton q
  have : IsModification πₚ := 𝔪[p].isModification_blowupToBase hdense'
  have : IsModification π_q := 𝔪[q].isModification_blowupToBase hdense
  have : IsModification (g ≫ π_q) := hcomm.symm ▸ inferInstanceAs (IsModification (πₚ ≫ f))
  have : IsModification g := IsModification.of_comp_right g π_q
  have : IrreducibleSpace 𝔪[q].blowup := (IsModification.birational π_q).irreducibleSpace
  have : IsRegular 𝔪[p].blowup := isRegular_blowup_closed_point hdp hp
  have : IsRegular 𝔪[q].blowup := isRegular_blowup_closed_point hdq hq
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have : IsIntegral 𝔪[q].blowup := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Surjective πₚ := surjective_blowupToBase_point hp hdp
  have hE : (Eₚ).IsExceptionalCurveOfFirstKind :=
    X.ker_fromSpecResidueField_eq_vanishingIdeal p ▸
      isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hdp
  have hF : (E_q).IsExceptionalCurveOfFirstKind :=
    Y.ker_fromSpecResidueField_eq_vanishingIdeal q ▸
      isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint q hq hdq
  have hmap : Set.MapsTo g ((Eₚ).support : Set 𝔪[p].blowup)
      ((E_q).support : Set 𝔪[q].blowup) := by
    rw [← range_subschemeι, ← range_subschemeι, range_subschemeι_comap_pointBlowup hp,
      range_subschemeι_comap_pointBlowup hq]
    intro x hx
    have hx' : πₚ x = p := hx
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, comp_apply, hx', hpoint] using
      congrArg (fun a : 𝔪[p].blowup ⟶ Y ↦ a x) hcomm
  let := hE.isIntegral_subscheme
  let := hF.isIntegral_subscheme
  by_contra hnc
  obtain ⟨e, he⟩ := hF.exists_iso_of_nonconstant_over_isoLocus g hmap hnc
    (genericPoint (E_q).subscheme)
    (g.mem_isoLocus_of_coheight_eq_one hF.isEffectiveCartier.coheight_subschemeι_genericPoint)
  exact hn (f.mem_isoLocus_of_exceptional_curve_isomorphism hp hq g hcomm hE hF e he.symm)

/-- Over a point in the centre of a modification between regular schemes, a morphism
completing the square of point blowups descends uniquely through the source point blowup.
The descended map still lifts the lower modification to the target point blowup. -/
theorem existsUnique_descended_lift_of_mem_centre [IsRegular X] [IsRegular Y]
    [IrreducibleSpace Y] (f : X ⟶ Y) [IsModification f]
    (hp : IsClosed ({p} : Set X)) (hq : IsClosed ({q} : Set Y))
    (hdp : ringKrullDim (X.presheaf.stalk p) = 2)
    (hdq : ringKrullDim (Y.presheaf.stalk q) = 2)
    (g : 𝔪[p].blowup ⟶ 𝔪[q].blowup)
    (hcomm : g ≫ π_q = πₚ ≫ f) (hpoint : f p = q) (hc : q ∈ f.centre) :
    ∃! g' : X ⟶ 𝔪[q].blowup, πₚ ≫ g' = g ∧ g' ≫ π_q = f := by
  let : X.Over Y := ⟨f⟩
  let : 𝔪[q].blowup.Over Y := ⟨π_q⟩
  obtain ⟨g', ⟨hg', hbase⟩, huniq⟩ := existsUnique_comp_eq_pointBlowup_over hp hdp g hcomm
    (f.range_exceptional_subsingleton_of_mem_centre hp hq hdp hdq g hcomm hpoint hc)
  exact ⟨g', ⟨hg', hbase.comp_over⟩, fun h hh ↦ huniq h ⟨hh.1, ⟨hh.2⟩⟩⟩

end AlgebraicGeometry.Scheme.Hom
