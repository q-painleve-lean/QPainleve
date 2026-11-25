/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.InternalIndices
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering

import QPainleve.AlgebraicGeometry.Curves.Node.Comap
import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Cycle
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Numbered boundaries of complexity zero under contraction

A specified point-blowup tower from a numbered anticanonical cycle of complexity
zero has only nodal steps. Numbering the schematic image gives the nonnegativity
needed to exclude internal steps, and the original ideal is the reduced total
transform of the schematic image.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u v

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)]

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" X "]" => mk (QPainleve.canonicalBundle k X 2)

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [Module.Finite ℤ (Additive (LineBundleClass X))]

/-- A complexity-zero anticanonical cycle descends along a specified closed-point
tower to a numbered anticanonical cycle of complexity zero. Every step of the
tower is nodal for the image boundary, and its reduced total transform is the
given boundary under the comparison isomorphism. -/
theorem exists_numbering_of_boundaryComplexity_eq_zero_of_iso
    {Y Z : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y} (hT : IsClosedPointTower X T)
    [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (e : Z ≅ Y) {f : Z ⟶ X} [f.IsOver S] (he : e.hom ≫ T.toBase = f)
    {B : Z.IdealSheafData} (hB : B.IsEffectiveCartier) [PrestableFamily (B.subscheme ↘ S)]
    {m : ℕ} [NeZero m] {ι : Type v} {a : ι → (B.subscheme ↘ S).smoothLocus}
    (A : Scheme.NodalCycleNumbering a m) (hcan : mk hB.toInvertibleSheaf = K[Z])
    (hzero : B.boundaryComplexity = 0) :
    let D := B.map f
    IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T ∧ (D.comap f).radical = B ∧
      D.boundaryComplexity = 0 ∧
      ∃ (hD : D.IsEffectiveCartier) (_ : PrestableFamily (D.subscheme ↘ S)),
        mk hD.toInvertibleSheaf = K[X] ∧
        ∃ (l : ℕ) (_ : NeZero l)
          (C : Scheme.NodalCycleNumbering
            (fun x : PEmpty.{v + 1} ↦ x.elim : PEmpty.{v + 1} → (D.subscheme ↘ S).smoothLocus) l)
          (g : B.subscheme ⟶ D.subscheme),
          g ≫ D.subschemeι = B.subschemeι ≫ f ∧ g.IsOrientedCycleSubdivision A C := by
  obtain ⟨hD, hpre, hcanD, l, hl, C, g, hg, hsub⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso e he hB A hcan
  let := hpre
  let := hl
  have hnonneg := (B.map f).boundaryComplexity_nonneg_of_nodalCycleNumbering hD C
  let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X ↘ S)
  have hover : e.inv ≫ Z ↘ S = T.toBase ≫ X ↘ S := by
    rw [← comp_over f S, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  let : e.inv.IsOver S := ⟨hover⟩
  let B' := B.comap e.inv
  have hB' : B'.IsEffectiveCartier := hB.comap e.inv
  have hcan' : mk hB'.toInvertibleSheaf = K[Y] := by
    rw [← hB.pullback_mk_toInvertibleSheaf hB', hcan, pullback_mk, mk_pullback_canonicalBundle]
  have hmap : B'.map T.toBase = B.map f := by
    have hp := B.comap_map_of_isOpenImmersion e.hom
    have h := congrArg (fun J : Z.IdealSheafData ↦ J.comap e.inv) hp
    simpa only [← map_comp, he, ← comap_comp, Iso.inv_hom_id, comap_id] using
      congrArg (fun J : Y.IdealSheafData ↦ J.map T.toBase) h.symm
  have hN : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ Z ↘ S) := by
    rw [← B.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hN' := hN.comap_of_etale e.inv
  rw [hover] at hN'
  have hzero' : B'.boundaryComplexity = 0 :=
    (boundaryComplexity_comap_iso e.symm B).trans hzero
  obtain ⟨hz, hnodal, htotal⟩ :=
    hT.isNodalBoundaryTower_of_boundaryComplexity_eq_zero k hB' hN' hzero'
      (hmap.symm ▸ hnonneg) hcan'
  rw [hmap] at hz hnodal htotal
  refine ⟨hnodal, ?_, hz, hD, hpre, hcanD, l, hl, C, g, hg, hsub⟩
  simpa only [← radical_comap_of_isOpenImmersion, ← comap_comp, he, B',
    Iso.hom_inv_id, comap_id] using congrArg (fun J : Y.IdealSheafData ↦ J.comap e.hom) htotal

end QPainleve.BlowupTower.IsClosedPointTower
