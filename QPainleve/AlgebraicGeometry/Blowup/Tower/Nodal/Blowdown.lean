/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.SmoothProjective
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Contracting a specified nodal boundary component

An exceptional curve contained in a nodal anticanonical boundary contracts to a
closed node of the schematic image boundary. The contraction records the point
blowup and its reduced total transform. On a rational surface one can recognize
the exceptional component from its Picard intersections, which permits the same
contraction after changing the centers in a marked toric presentation.

The construction uses Castelnuovo contraction, as in the
[Stacks Project, Lemma 54.16.9](https://stacks.math.columbia.edu/tag/0C2N), and
`IsEffectiveCartier.anticanonical_nodal_boundary_point_blowdown`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)]
  {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {B : Y.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" W "]" => LineBundleClass.mk (canonicalBundle k W 2)
local notation "J[" p "]" => vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
local notation "T[" p "]" => BlowupTower.nil.snoc (J[p])

omit [Y.IsProjectiveOver k] in
private theorem nodal_blowdown_of_iso
    {X : Scheme.{u}} [X.Over S] [X.IsProjectiveOver k] [IsIntegral X]
    [SmoothOfRelativeDimension 2 (X ↘ S)]
    {p : X} {f : Y ⟶ X} [f.IsOver S] (hp : IsClosed ({p} : Set X))
    (e : Y ≅ (J[p]).blowup) (he : e.hom ≫ (J[p]).blowupToBase = f)
    (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ Y ↘ S))
    (hK : LineBundleClass.mk hB.toInvertibleSheaf = K[Y])
    (hF : ((J[p]).comap f).support ≤ B.support) :
    let D := B.map f
    ∃ hD : D.IsEffectiveCartier, LineBundleClass.mk hD.toInvertibleSheaf = K[X] ∧
      AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S) ∧
      D.IsNodeOfReducedBoundary (X ↘ S) p ∧ D.comap f = B * (J[p]).comap f := by
  let π := (J[p]).blowupToBase
  let : (J[p]).blowup.Over S := ⟨π ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 ((J[p]).blowup ↘ S) :=
    smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
  have hπ : e.inv ≫ f = π := by rw [← he, Iso.inv_hom_id_assoc]
  let : e.inv.IsOver S := ⟨by rw [← comp_over f S, ← Category.assoc, hπ]; rfl⟩
  let B' := B.comap e.inv
  have hB' : B'.IsEffectiveCartier := hB.comap e.inv
  obtain ⟨d, hd⟩ := B.exists_iso_of_comap_eq_ker e.symm B'.subschemeι B'.ker_subschemeι.symm
  simp only [Iso.symm_hom] at hd
  have hN' := hN.comp_of_etale d.hom
  rw [← Category.assoc, hd, Category.assoc, comp_over e.inv S] at hN'
  have hK' : LineBundleClass.mk hB'.toInvertibleSheaf = K[(J[p]).blowup] := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hK, pullback_mk, mk_pullback_canonicalBundle]
  have hNπ : AtWorstNodalOfRelativeDimensionOne (B'.subschemeι ≫ π ≫ X ↘ S) := hN'
  obtain ⟨hD, hcan, hnodal, htotal, hnode⟩ :=
    hB'.anticanonical_nodal_boundary_point_blowdown k hp hNπ hK'
  have hF' : ((J[p]).comap π).support ≤ B'.support := by
    have h := ((J[p]).comap f).support_comap e.inv
    rw [← comap_comp, hπ] at h
    rw [h]
    dsimp only [B']
    rw [B.support_comap e.inv, ← SetLike.coe_subset_coe, Closeds.coe_preimage, Closeds.coe_preimage]
    exact Set.preimage_mono (SetLike.coe_subset_coe.mpr hF)
  have hd' : d.hom ≫ B.subschemeι ≫ f = B'.subschemeι ≫ π := by
    rw [← Category.assoc, hd, Category.assoc, hπ]
  have hmap : B'.map (J[p]).blowupToBase = B.map f := by
    rw [map, ← hd', Scheme.Hom.ker_comp_of_isIso, map]
  have htot := congrArg (fun D : (J[p]).blowup.IdealSheafData ↦ D.comap e.hom) htotal
  simp only [comap_mul, B', ← comap_comp, he, Iso.hom_inv_id, comap_id] at htot
  exact ⟨hmap ▸ hD, by rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hD hmap.symm, hcan],
    hmap ▸ hnodal, hmap ▸ hnode.mp hF', hmap ▸ htot⟩

/-- A specified exceptional curve contained in a nodal anticanonical boundary
contracts to a closed node. The blowdown realizes a one-step nodal tower over
the schematic image boundary, with the prescribed curve as the exceptional fiber.
The other primes map bijectively to the new boundary primes. -/
theorem exists_nodal_boundary_blowdown [IsIntegral Y]
    (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ Y ↘ S))
    (hK : LineBundleClass.mk hB.toInvertibleSheaf = K[Y])
    {E : Y.IdealSheafData} (hE : E.IsExceptionalCurveOfFirstKind)
    (hEB : E.support ≤ B.support) :
    ∃ (X : Scheme.{u}) (s : X ⟶ S) (f : Y ⟶ X) (p : X),
      letI : X.Over S := ⟨s⟩
      ∃ (_ : IsIntegral X) (_ : X.IsProjectiveOver k) (hSm : SmoothOfRelativeDimension 2 s),
        let : SmoothOfRelativeDimension 2 (X ↘ S) := hSm
        f.IsOver S ∧ IsModification f ∧ IsClosed ({p} : Set X) ∧ f.centre = {p} ∧
        (J[p]).comap f = E ∧
        ∃ e : Y ≅ (J[p]).blowup, e.hom ≫ (T[p]).toBase = f ∧
          let D := B.map f
          ∃ hD : D.IsEffectiveCartier,
            LineBundleClass.mk hD.toInvertibleSheaf = K[X] ∧
            AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) ∧
            IsNodalBoundaryTower D s (𝟙 X) (T[p]) ∧ (D.comap f).radical = B ∧
            Set.BijOn f (B.boundaryPrimes \ E.support) D.boundaryPrimes := by
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  obtain ⟨X, s, f, p, hX, hproj, hSm, hover, hmod, hp, hc, hF, -, e, he⟩ :=
    hE.exists_smooth_projective_contraction (k := k)
  let : X.Over S := ⟨s⟩
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hSm
  let : f.IsOver S := hover
  let I := Scheme.Hom.ker (X.fromSpecResidueField p)
  have hIJ : I = J[p] := X.ker_fromSpecResidueField_eq_vanishingIdeal p
  let a : I.blowup ≅ (J[p]).blowup :=
    blowupIso (Iso.refl X) (hIJ.trans (comap_id _).symm)
  have ha : a.hom ≫ (J[p]).blowupToBase = I.blowupToBase := by
    simp only [a, blowupIso_hom_blowupToBase, Iso.refl_hom, Category.comp_id]
  have hef : (e ≪≫ a).hom ≫ (J[p]).blowupToBase = f := by
    rw [Iso.trans_hom, Category.assoc, ha, he]
  have hExc : (J[p]).comap f = E := hIJ ▸ hF
  obtain ⟨hD, hcan, hnodal, hnode, htotal⟩ :=
    nodal_blowdown_of_iso hp (e ≪≫ a) hef hB hN hK (hExc.symm ▸ hEB)
  let D := B.map f
  have hsupp : (D.comap f).support = B.support := by
    dsimp only [D]
    rw [htotal, support_mul, hExc, sup_eq_left.mpr hEB]
  have hred : (D.comap f).radical = B := by
    rw [← vanishingIdeal_support, hsupp, vanishingIdeal_support,
      B.isReduced_subscheme_iff_radical_eq.mp hN.isReduced]
  have hcut : {y : Y | f y ≠ p} = (E.support : Set Y)ᶜ := by
    rw [← hExc, support_comap, Closeds.coe_preimage, coe_support_vanishingIdeal,
      Closeds.coe_mk, hp.closure_eq]
    rfl
  have hbij := D.bijOn_boundaryPrimes_comap_off_point f
    (by rw [coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) s hp]; decide)
    (fun x hx ↦ by
      rw [← SetLike.mem_coe, ← Scheme.Hom.compl_centre, hc]
      exact hx)
  rw [boundaryPrimes_eq_of_support_eq hsupp, hcut, ← Set.sdiff_eq] at hbij
  exact ⟨X, s, f, p, hX, hproj, hSm, hover, hmod, hp, hc, hExc, e ≪≫ a,
    by simpa only [toBase_snoc, toBase_nil, Category.comp_id] using hef,
    hD, hcan, hnodal, IsNodalBoundaryTower.of_node hp hnode, hred, hbij⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
