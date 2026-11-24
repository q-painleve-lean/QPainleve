/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.Geometry.Toric.Fan.Boundary.Basic
public import QPainleve.Geometry.Toric.Fan.Smooth
public import QPainleve.Geometry.Toric.Fan.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction

/-!
# Pole ideals of toric surface subdivisions

The pullback of the reduced toric boundary under a regular subdivision is the
new reduced boundary times the ramification ideal. Consequently, on any smooth
integral surface dominating a common toric refinement, a specified pole ideal
for one projection is also the pole ideal for the other projection.

This is the log pullback identity for the toric steps in the proof of Theorem 8.4
in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Ω : Fan i}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "s[" Φ "]" => (X[Φ] ↘ S)
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "D[" A "," h "]" => Fan.boundaryIdeal A (Fan.IsComplete.nonempty_cones h)

/-- Under a regular subdivision over a complete toric surface, the pullback
of the boundary ideal is the new boundary ideal times the ramification ideal. -/
theorem IsSubdivision.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf
    (H : Ω.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular)
    (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2) :
    letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
    letI : Smooth s[Ω] := (Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ).smooth
    (D[Φ, hc]).comap π[H] = D[Ω, H.isComplete_iff.mpr hc] * ramificationIdealSheaf ℂ π[H] := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 s[Φ] :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 s[Ω] :=
    hN ▸ Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
  let : Smooth s[Φ] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian X[Φ] := isNoetherian_of_finiteType s[Φ]
  obtain ⟨n, Y, T, e, hT, he, -, -⟩ :=
    H.exists_toric_subdivision_blowup_tower hΦ hΩ hc.nonempty_cones hN
  have h := hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso (k := ℂ)
    (Φ.isEffectiveCartier_boundaryIdeal hΦ hc hN)
    (Φ.atWorstNodalOfRelativeDimensionOne_boundary hΦ hc hN) e π[H] he
  rwa [H.radical_comap_boundaryIdeal inferInstance inferInstance] at h

/-- The ramification ideal of a regular toric surface subdivision is effective Cartier. -/
theorem IsSubdivision.isEffectiveCartier_ramificationIdealSheaf
    (H : Ω.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular)
    (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2) :
    letI : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
    letI : Smooth s[Ω] := (Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ).smooth
    (ramificationIdealSheaf ℂ π[H]).IsEffectiveCartier := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  let : Smooth s[Ω] := (Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ).smooth
  let hcΩ := H.isComplete_iff.mpr hc
  have hD := Ω.isEffectiveCartier_boundaryIdeal hΩ hcΩ hN
  have hTotal := (Φ.isEffectiveCartier_boundaryIdeal hΦ hc hN).comap_of_isDominant π[H]
  have h := H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hΦ hΩ hc hN
  rw [h, mul_comm] at hTotal
  simpa only [hD.mul_colon_cancel_right] using
    hTotal.colon hD.locallyPrincipal (fun U ↦ Ideal.mul_le_right)

/-- A dominant map from a smooth integral surface and its composite with a regular toric
subdivision have the same pole factorizations along the respective toric boundaries. -/
theorem IsSubdivision.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff
    (H : Ω.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular)
    (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2)
    {Z : Scheme} [Z.Over S] [IsIntegral Z] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (g : Z ⟶ X[Ω]) [g.IsOver S] [IsDominant g] (P : Z.IdealSheafData) :
    letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (D[Φ, hc]).comap (g ≫ π[H]) = P * ramificationIdealSheaf ℂ (g ≫ π[H]) ↔
      (D[Ω, H.isComplete_iff.mpr hc]).comap g = P * ramificationIdealSheaf ℂ g := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ω.cones := H.nonempty_cones_of_nonempty hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 s[Φ] :=
    hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 s[Ω] :=
    hN ▸ Ω.smoothOfRelativeDimension_algebraicRealizationStructureMap hΩ
  let : Smooth s[Ω] := SmoothOfRelativeDimension.smooth 2 _
  have hRam := (H.isEffectiveCartier_ramificationIdealSheaf hΦ hΩ hc hN).comap_of_isDominant g
  exact TauCeti.AlgebraicGeometry.comap_eq_mul_ramificationIdealSheaf_comp_iff ℂ g π[H] 2 hRam
    (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hΦ hΩ hc hN)

/-- On a smooth integral surface mapping dominantly to a common regular subdivision,
the two composites with the toric projections have the same pole ideal whenever
either has a pole factorization. This comparison is for the specified morphisms over
`ℂ` and holds for any ideal on the resolving surface. -/
theorem comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_iff_of_common_subdivision
    (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ)
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hΩ : Ω.IsRegular)
    (hc : Φ.IsComplete) (hN : Module.finrank ℤ N = 2)
    {Z : Scheme} [Z.Over S] [IsIntegral Z] [SmoothOfRelativeDimension 2 (Z ↘ S)]
    (g : Z ⟶ X[Ω]) [g.IsOver S] [IsDominant g] (P : Z.IdealSheafData) :
    let hc' := K.isComplete_iff.mp (H.isComplete_iff.mpr hc)
    letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (D[Φ, hc]).comap (g ≫ π[H]) = P * ramificationIdealSheaf ℂ (g ≫ π[H]) ↔
      (D[Ψ, hc']).comap (g ≫ π[K]) = P * ramificationIdealSheaf ℂ (g ≫ π[K]) := by
  let hc' := K.isComplete_iff.mp (H.isComplete_iff.mpr hc)
  exact (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff hΦ hΩ hc hN g P).trans
    (K.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff hΨ hΩ hc' hN g P).symm

/-- For towers with projections factoring through a common regular toric subdivision,
the first tower's pole ideal is also the pole ideal for its map to the
common refinement and for its composite to the second base.
On the second tower the pole ideal is pulled back along the inverse source isomorphism. -/
theorem IsSubdivision.pole_ideal_of_blowup_towers
    (H : Ω.IsSubdivision Φ) (K : Ω.IsSubdivision Ψ)
    (hΦ : Φ.IsRegular) (hΩ : Ω.IsRegular) (hΨ : Ψ.IsRegular)
    (hc : Φ.IsComplete) (hcΩ : Ω.IsComplete) (hcΨ : Ψ.IsComplete)
    (hN : Module.finrank ℤ N = 2)
    [SmoothOfRelativeDimension 2 (X[Φ] ↘ S)] [SmoothOfRelativeDimension 2 (X[Ψ] ↘ S)]
    {Y Z : Scheme} {m n : ℕ} [IsIntegral Y]
    {T : QPainleve.BlowupTower X[Φ] m Y} (hT : IsClosedPointTower X[Φ] T)
    {U : QPainleve.BlowupTower X[Ψ] n Z} (hU : IsClosedPointTower X[Ψ] U)
    (q : Y ⟶ X[Ω]) [IsDominant q] (k : Y ≅ Z)
    (hq : q ≫ π[H] = T.toBase) (hq' : q ≫ π[K] = k.hom ≫ U.toBase) :
    letI : Y.Over S := ⟨T.toBase ≫ X[Φ] ↘ S⟩
    letI : T.toBase.IsOver S := ⟨rfl⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X[Φ] ↘ S)
    letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    ∃ (_ : q.IsOver S) (_ : (k.hom ≫ U.toBase).IsOver S),
      ∀ P : Y.IdealSheafData,
        D[Φ, hc].comap T.toBase = P * hT.ramificationIdealSheafToBase ℂ →
          D[Ω, hcΩ].comap q = P * ramificationIdealSheaf ℂ q ∧
          D[Ψ, hcΨ].comap (k.hom ≫ U.toBase) = P * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) ∧
          D[Ψ, hcΨ].comap U.toBase = P.comap k.inv * hU.ramificationIdealSheafToBase ℂ := by
  let : Y.Over S := ⟨T.toBase ≫ X[Φ] ↘ S⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension (X[Φ] ↘ S)
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : q.IsOver S := ⟨by
    rw [Ω.algebraicRealization_over,
      ← H.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap, ← Category.assoc, hq,
      ← Φ.algebraicRealization_over, comp_over]⟩
  let : (k.hom ≫ U.toBase).IsOver S := ⟨hq' ▸ comp_over (q ≫ π[K]) S⟩
  refine ⟨‹q.IsOver S›, ‹(k.hom ≫ U.toBase).IsOver S›, fun P hP ↦ ?_⟩
  have hΦq : D[Φ, hc].comap (q ≫ π[H]) = P * ramificationIdealSheaf ℂ (q ≫ π[H]) :=
    (congrArg D[Φ, hc].comap hq).trans (hP.trans (congrArg (P * ·)
      ((hT.ramificationIdealSheafToBase_def ℂ).trans (ramificationIdealSheaf_congr ℂ hq.symm))))
  have hΩq := (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff hΦ hΩ hc hN q P).mp hΦq
  have hΨq :=
    (K.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff hΨ hΩ hcΨ hN q P).mpr hΩq
  have hΨk : D[Ψ, hcΨ].comap (k.hom ≫ U.toBase) = P * ramificationIdealSheaf ℂ (k.hom ≫ U.toBase) :=
    (congrArg D[Ψ, hcΨ].comap hq'.symm).trans
      (hΨq.trans (congrArg (P * ·) (ramificationIdealSheaf_congr ℂ hq')))
  let : Z.Over S := ⟨U.toBase ≫ X[Ψ] ↘ S⟩
  let : U.toBase.IsOver S := ⟨rfl⟩
  let : k.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (comp_over (k.hom ≫ U.toBase) S)⟩
  let : SmoothOfRelativeDimension 2 (Z ↘ S) := hU.smoothOfRelativeDimension (X[Ψ] ↘ S)
  refine ⟨hΩq, hΨk, ?_⟩
  simpa only [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id, hU.ramificationIdealSheafToBase_def ℂ]
    using (comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ k.hom U.toBase 2).mp hΨk

end TauCeti.Toric.Fan
