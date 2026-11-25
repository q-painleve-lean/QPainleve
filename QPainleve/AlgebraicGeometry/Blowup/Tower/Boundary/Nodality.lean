/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.NodalContraction
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Anticanonical

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Nodal boundary descent through point-blowup towers

The schematic image of a nodal anticanonical boundary along a closed-point tower
on a smooth projective surface is nodal. This applies to the projection from a
specified source identified with the top of the tower over the ground field.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

namespace QPainleve.BlowupTower.IsClosedPointTower

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] [NeZero (2 : k)] {X Y : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n Y}

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)
local notation "K(" W ")" => LineBundleClass.mk (QPainleve.canonicalBundle k W 2)

/-- The schematic image of a nodal anticanonical boundary along a specified
closed-point blowup tower is nodal. The centers can be infinitely near. -/
theorem atWorstNodalOfRelativeDimensionOne_anticanonical_boundary_blowdown
    (hT : IsClosedPointTower X T) {B : Y.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ T.toBase ≫ s)) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    LineBundleClass.mk hB.toInvertibleSheaf = K(Y) →
      AtWorstNodalOfRelativeDimensionOne ((B.map T.toBase).subschemeι ≫ s) := by
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  induction hT with
  | nil =>
    dsimp only
    intro _
    rw [toBase_nil, map_id]
    rwa [toBase_nil, Category.id_comp] at hnodal
  | @snoc m W U I hU p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
    let : W.Over S := ⟨U.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s
    have : IsIntegral W := hU.isIntegral s
    have : W.IsProjectiveOver k := U.isProjectiveOver k
    dsimp only
    intro hcan
    -- The top structure map is indexed by the tower projection in the induction.
    have hclass (f : I.blowup ⟶ S) (hf : f = I.blowupToBase ≫ (W ↘ S))
        (hs : SmoothOfRelativeDimension 2 f) :
        @QPainleve.canonicalBundle k _ I.blowup ⟨f⟩ 2 hs =
          @QPainleve.canonicalBundle k _ I.blowup ⟨I.blowupToBase ≫ (W ↘ S)⟩ 2
            (smoothOfRelativeDimension_blowup_closed_point (W ↘ S) hp) := by
      subst f
      rfl
    have hbase : (U.snoc I).toBase ≫ s = I.blowupToBase ≫ (W ↘ S) := by
      rw [toBase_snoc, Category.assoc]
      rfl
    rw [hclass _ hbase _] at hcan
    have hnodalPoint : AtWorstNodalOfRelativeDimensionOne
        (B.subschemeι ≫ I.blowupToBase ≫ (W ↘ S)) := hbase ▸ hnodal
    obtain ⟨hD, hcanD, hnodalD, -, -⟩ :=
      hB.anticanonical_nodal_boundary_point_blowdown k hp hnodalPoint hcan
    rw [toBase_snoc, map_comp]
    exact ih hD hnodalD hcanD

/-- A nodal anticanonical boundary remains nodal and anticanonical under a
projection identified over the field with a closed-point blowup tower. Its total
transform adds the ramification divisor of the projection. -/
theorem anticanonical_nodal_boundary_blowdown
    (hT : IsClosedPointTower X T)
    {Z : Scheme.{u}} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (a : Z ≅ Y) {f : Z ⟶ X} [f.IsOver S] (ha : a.hom ≫ T.toBase = f)
    {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ (Z ↘ S)))
    (hcan : LineBundleClass.mk hB.toInvertibleSheaf = K(Z)) :
    let D := B.map f
    ∃ hD : D.IsEffectiveCartier, LineBundleClass.mk hD.toInvertibleSheaf = K(X) ∧
      AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) ∧
      D.comap f = B * (hT.ramificationIdealSheafToBase k).comap a.hom := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have hover : a.inv ≫ (Z ↘ S) = T.toBase ≫ s := by
    rw [← comp_over f S, ← ha, ← Category.assoc, Iso.inv_hom_id_assoc]
  have : a.inv.IsOver S := ⟨hover⟩
  let B' := B.comap a.inv
  have hB' : B'.IsEffectiveCartier := hB.comap a.inv
  obtain ⟨d, hd⟩ := B.exists_iso_of_comap_eq_ker a.symm B'.subschemeι B'.ker_subschemeι.symm
  simp only [Iso.symm_hom] at hd
  have hnodal' := hnodal.comp_of_etale d.hom
  rw [← Category.assoc, hd, Category.assoc, hover] at hnodal'
  have hcan' : LineBundleClass.mk hB'.toInvertibleSheaf = K(Y) := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hBmap := congrArg (fun A : Z.IdealSheafData ↦ A.comap a.inv)
    (B.comap_map_of_isOpenImmersion a.hom)
  rw [← comap_comp, Iso.inv_hom_id, comap_id] at hBmap
  have hnodalD := hT.atWorstNodalOfRelativeDimensionOne_anticanonical_boundary_blowdown k
    hB' hnodal' hcan'
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have : IsReduced B.subscheme := hnodal.isReduced
  obtain ⟨hD, -, hcanD, htotal⟩ := hT.anticanonical_boundary_blowdown_of_iso k a ha hB hcan
  dsimp only [B'] at hnodalD
  rw [← hBmap, ← map_comp, ha] at hnodalD
  exact ⟨hD, hcanD, hnodalD, htotal⟩

end QPainleve.BlowupTower.IsClosedPointTower
