/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.Comap
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.Geometry.Toric.Fan.Presentation.InternalBlowup
import QPainleve.Geometry.Toric.Fan.Presentation.NodalBlowup
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Toric presentations along closed-point towers

A toric presentation of the schematic image of a nodal anticanonical boundary
extends to the original pair along a specified closed-point blowup tower.
Boundary descent detects the nodal and smooth centers at each stage.
This is the reduction to a minimal surface in
[Gross, Hacking and Keel, *Mirror symmetry for log Calabi–Yau surfaces I*,
Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} (b : Module.Basis (Fin 2) ℤ N)

namespace QPainleve.BlowupTower.IsClosedPointTower

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [NeZero (2 : k₀)]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "K(" W ")" => LineBundleClass.mk (QPainleve.canonicalBundle k₀ W 2)

variable {b} [X.Over (Spec (.of k₀))] [X.IsProjectiveOver k₀] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))] {n : ℕ} {T : BlowupTower X n Y}

local notation "s" => (X ↘ S)

/-- If the schematic image of a nodal anticanonical boundary along a
closed-point blowup tower admits a toric presentation, then the original pair
does as well. The tower may mix nodal and internal stages, including infinitely
near centers. -/
theorem hasToricPresentation_of_closedPointTower (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    LineBundleClass.mk hB.toInvertibleSheaf = K(Y) →
    (B.map T.toBase).HasToricPresentation s b i →
    B.HasToricPresentation (T.toBase ≫ s) b i := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  induction hT with
  | nil =>
    simpa only [toBase_nil, map_id, Category.id_comp] using fun _ h ↦ h
  | @snoc m W U J hU p hp hJ ih =>
    have hcenter := hJ.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure ({p} : Set W)) isClosed_closure)
    let π := I.blowupToBase
    let : W.Over S := ⟨U.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s
    have : IsIntegral W := hU.isIntegral s
    have : W.IsProjectiveOver k₀ := U.isProjectiveOver k₀
    have : IsNoetherian W := U.isNoetherian
    intro _ _ hcan h
    have hbase : (U.snoc I).toBase ≫ s = π ≫ (W ↘ S) := by
      rw [toBase_snoc, Category.assoc]
      rfl
    -- Pointwise descent uses the last blowup followed by the intermediate structure map.
    have hclass (f : I.blowup ⟶ S) (hf : f = π ≫ (W ↘ S))
        (hs : SmoothOfRelativeDimension 2 f) :
        @QPainleve.canonicalBundle k₀ _ I.blowup ⟨f⟩ 2 hs =
          @QPainleve.canonicalBundle k₀ _ I.blowup ⟨π ≫ (W ↘ S)⟩ 2
            (smoothOfRelativeDimension_blowup_closed_point (W ↘ S) hp) := by
      subst f
      rfl
    rw [hclass _ hbase _] at hcan
    have hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ (W ↘ S)) :=
      hbase ▸ hN
    let D := B.map π
    have hDpres : (D.map U.toBase).HasToricPresentation s b i := by
      simpa only [toBase_snoc, map_comp] using h
    rw [hbase]
    by_cases hE : (I.comap π).support ≤ B.support
    · obtain ⟨hD, hcanD, hN', htotal, hnode⟩ :=
        hB.anticanonical_nodal_boundary_point_blowdown k₀ hp hnodal hcan
      have hBD : (D.comap π).radical = B := by
        rw [← vanishingIdeal_support, htotal, support_mul, sup_eq_left.mpr hE,
          vanishingIdeal_support, B.isReduced_subscheme_iff_radical_eq.mp hnodal.isReduced]
      rw [← hBD]
      exact (ih hD hN' hcanD hDpres).nodalBlowup hp (hnode.mp hE)
    · obtain ⟨hD, hcanD, hN', _, _, hstrict, _, ⟨q, hq, hs⟩, -⟩ :=
        hB.internalBlowdown_of_anticanonical k₀ hp hE hnodal hcan
      have : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      have hfp : LocallyOfFinitePresentation (D.subschemeι ≫ (W ↘ S)) :=
        TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier hD
      exact hstrict ▸
        (ih hD hN' hcanD hDpres).internalBlowup hN' hp hq
          ((@Scheme.Hom.mem_smoothLocus _ _ _ hfp q).mp hs)

/-- The closed-point tower comparison also applies when the original surface is
identified with the top by an isomorphism over the ground field, as in the
minimal-model theorem. The boundary on the base is the schematic image along
the specified projection. -/
theorem hasToricPresentation_of_closedPointTower_of_iso (hT : IsClosedPointTower X T)
    {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (a : Z ≅ Y) (ha : a.hom ≫ T.toBase ≫ s = Z ↘ S)
    {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ (Z ↘ S)))
    (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K(Z))
    (h : (B.map (a.hom ≫ T.toBase)).HasToricPresentation s b i) :
    B.HasToricPresentation (Z ↘ S) b i := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have hover : a.inv ≫ (Z ↘ S) = T.toBase ≫ s := by
    rw [← ha, Iso.inv_hom_id_assoc]
  have : a.inv.IsOver S := ⟨hover⟩
  let B' := B.comap a.inv
  have hB' : B'.IsEffectiveCartier := hB.comap a.inv
  have hN' := hN.comap_of_etale a.inv
  rw [hover] at hN'
  have hcan' : LineBundleClass.mk hB'.toInvertibleSheaf = K(Y) := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk,
      mk_pullback_canonicalBundle]
  have hmap : B' = B.map a.hom := by
    have hcomap := congrArg (fun J : Z.IdealSheafData ↦ J.comap a.inv)
      (B.comap_map_of_isOpenImmersion a.hom)
    rw [← comap_comp, Iso.inv_hom_id, comap_id] at hcomap
    exact hcomap.symm
  have h' : (B'.map T.toBase).HasToricPresentation s b i := by rwa [hmap, ← map_comp]
  exact (hT.hasToricPresentation_of_closedPointTower k₀ hB' hN' hcan' h').of_comap_iso ha

end QPainleve.BlowupTower.IsClosedPointTower
