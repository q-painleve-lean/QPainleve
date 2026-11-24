/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Contraction
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Anticanonical boundaries on closed-point towers

The image of a reduced anticanonical divisor along a closed-point blowup tower
is reduced anticanonical. Its total transform is the original divisor plus the
ramification divisor of the projection. The formula applies to mixed internal
and boundary contractions, including towers with infinitely near centers.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

namespace QPainleve.BlowupTower.IsClosedPointTower

universe u

variable (k : Type u) [Field k] [PerfectField k] {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {n : ℕ} {T : BlowupTower X n Y}

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)
local notation "K(" W ")" => mk (QPainleve.canonicalBundle k W 2)

/-- A reduced anticanonical divisor on the top of a specified closed-point blowup
tower has a reduced anticanonical schematic image. Its pullback is the original
divisor plus the ramification divisor of the tower projection. -/
theorem anticanonical_boundary_blowdown (hT : IsClosedPointTower X T)
    {B : Y.IdealSheafData} [IsReduced B.subscheme] (hB : B.IsEffectiveCartier) :
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    mk hB.toInvertibleSheaf = K(Y) →
    let D := B.map T.toBase
    ∃ hD : D.IsEffectiveCartier, IsReduced D.subscheme ∧ mk hD.toInvertibleSheaf = K(X) ∧
      D.comap T.toBase = B * hT.ramificationIdealSheafToBase k := by
  induction hT with
  | nil =>
    dsimp only
    intro hcan
    have hbase : (BlowupTower.nil (X := X)).toBase ≫ s = s := by
      rw [toBase_nil, Category.id_comp]
    have hclass (f : X ⟶ S) (hf : f = s) (hs : SmoothOfRelativeDimension 2 f) :
        @QPainleve.canonicalBundle k _ X ⟨f⟩ 2 hs = QPainleve.canonicalBundle k X 2 := by
      subst f
      rfl
    rw [hclass _ hbase (IsClosedPointTower.nil.smoothOfRelativeDimension s)] at hcan
    rw [toBase_nil, map_id, comap_id, ramificationIdealSheafToBase_nil, mul_top]
    exact ⟨hB, inferInstance, hcan, rfl⟩
  | @snoc m W U I hU p hp hI ih =>
    have hcenter := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    subst hcenter
    let I := vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)
    let : W.Over S := ⟨U.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s
    have : IsIntegral W := hU.isIntegral s
    have : IsNoetherian W := U.isNoetherian
    dsimp only
    intro hcan
    have hclass (f : I.blowup ⟶ S) (hf : f = I.blowupToBase ≫ (W ↘ S))
        (hs : SmoothOfRelativeDimension 2 f) :
        @QPainleve.canonicalBundle k _ I.blowup ⟨f⟩ 2 hs =
          @QPainleve.canonicalBundle k _ I.blowup ⟨I.blowupToBase ≫ (W ↘ S)⟩ 2
            (smoothOfRelativeDimension_blowup_closed_point (W ↘ S) hp) := by
      subst f
      rfl
    rw [hclass _ (by rw [toBase_snoc, Category.assoc]; rfl) _] at hcan
    obtain ⟨hD, hred, hcanD, htotal, -⟩ :=
      hB.anticanonical_boundary_point_blowdown k hp hcan
    let : IsReduced (B.map I.blowupToBase).subscheme := hred
    obtain ⟨hC, hredC, hcanC, htotalC⟩ := ih hD hcanD
    rw [toBase_snoc, map_comp]
    refine ⟨hC, hredC, hcanC, ?_⟩
    rw [comap_comp, htotalC, comap_mul, htotal, ramificationIdealSheafToBase_snoc, mul_assoc]

/-- The reduced anticanonical image and total-transform formula for a specified
projection identified with a closed-point blowup tower by an isomorphism over
the field. -/
theorem anticanonical_boundary_blowdown_of_iso (hT : IsClosedPointTower X T)
    {Z : Scheme.{u}} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (a : Z ≅ Y) {f : Z ⟶ X} [f.IsOver S] (ha : a.hom ≫ T.toBase = f)
    {B : Z.IdealSheafData} [IsReduced B.subscheme] (hB : B.IsEffectiveCartier)
    (hcan : mk hB.toInvertibleSheaf = K(Z)) :
    let D := B.map f
    ∃ hD : D.IsEffectiveCartier, IsReduced D.subscheme ∧ mk hD.toInvertibleSheaf = K(X) ∧
      D.comap f = B * (hT.ramificationIdealSheafToBase k).comap a.hom := by
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
  have haOver : a.hom ≫ (Y ↘ S) = (Z ↘ S) := by
    rw [← comp_over f S, ← ha, Category.assoc]
    rfl
  have : a.inv.IsOver S := ⟨by rw [← haOver, Iso.inv_hom_id_assoc]⟩
  let B' := B.comap a.inv
  have hB' : B'.IsEffectiveCartier := hB.comap a.inv
  have : IsReduced B'.subscheme := (B'.isReduced_subscheme_iff_radical_eq).mpr (by
    dsimp only [B']
    rw [radical_comap_of_isOpenImmersion, B.isReduced_subscheme_iff_radical_eq.mp inferInstance])
  have hcan' : mk hB'.toInvertibleSheaf = K(Y) := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk, mk_pullback_canonicalBundle]
  obtain ⟨hD, hred, hcanD, htotal⟩ := hT.anticanonical_boundary_blowdown k hB' hcan'
  have hBmap := congrArg (fun A : Z.IdealSheafData ↦ A.comap a.inv)
    (B.comap_map_of_isOpenImmersion a.hom)
  rw [← comap_comp, Iso.inv_hom_id, comap_id] at hBmap
  dsimp only
  rw [← ha, map_comp, hBmap]
  refine ⟨hD, hred, hcanD, ?_⟩
  rw [comap_comp, htotal, comap_mul, ← comap_comp, Iso.hom_inv_id, comap_id]

end QPainleve.BlowupTower.IsClosedPointTower
