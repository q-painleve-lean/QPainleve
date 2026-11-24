/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Subdivision
public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
public import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# The ordered boundary of a toric refinement

A regular fan subdivision lifts a numbering of the toric boundary to one
on the refined fan, with the ordered conductor branches inherited from
the nodal blowup tower. Each old ray retains the generic point of its
component under the boundary projection. The comparison uses
`IsSubdivision.exists_toric_subdivision_blowup_tower` and
`IsNodalBoundaryTower.exists_isOrientedCycleSubdivision_nodalBoundaryTower`.
-/

public section

open AlgebraicGeometry CategoryTheory
open QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "," h "]" => Fan.boundaryIdeal Φ h
local notation "C[" Φ "," h "]" => Scheme.IdealSheafData.subscheme D[Φ,h]

variable [PrestableFamily (C[Φ,hΦ₀] ↘ S)]
  {γ δ : Type*} {p : γ → (C[Φ,hΦ₀] ↘ S).smoothLocus}
  {n : ℕ} [NeZero n] (A : Scheme.NodalCycleNumbering p n)

variable (hΦ : Φ.IsRegular) (h : Ψ.IsSubdivision Φ) (hΨ : Ψ.IsRegular)

local notation "β" => h.boundaryMap hΨ₀ hΦ₀

section Components

variable [PrestableFamily (C[Ψ,hΨ₀] ↘ S)] {q : δ → (C[Ψ,hΨ₀] ↘ S).smoothLocus}

include hΦ hΨ in
/-- Any numbering of the refined boundary contains a component above each old
numbered component. Its ray is the lift of the original ray. -/
theorem IsSubdivision.exists_componentGenericPoint_lift
    {l : ℕ} [NeZero l] (U : Scheme.NodalCycleNumbering q l) (j : ZMod n) :
    ∃ j' : ZMod l, β (U.componentGenericPoint j') = A.componentGenericPoint j := by
  obtain ⟨ρ, hρ⟩ := (Φ.boundaryNormalizationComponentEquiv hΦ).surjective (A.component j)
  obtain ⟨j', hj'⟩ :=
    U.component.surjective (Ψ.boundaryNormalizationComponentEquiv hΨ (h.liftRay ρ))
  refine ⟨j', (D[Φ,hΦ₀]).subschemeι.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, h.boundaryMap_comp_subschemeι,
    Scheme.Hom.comp_apply, subschemeι_componentGenericPoint_eq_rayBoundaryPoint U hΨ j' _ hj',
    h.algebraicMap_rayBoundaryPoint_liftRay hΨ hΦ,
    subschemeι_componentGenericPoint_eq_rayBoundaryPoint A hΦ j ρ hρ.symm]

end Components

include hΦ hΨ in
/-- The boundary projection of a regular fan subdivision is an oriented
conductor subdivision for a numbering extending the original orientation.
The smooth marked points on the refined boundary may be chosen arbitrarily. -/
theorem IsSubdivision.exists_isOrientedCycleSubdivision_boundaryMap
    (hD₀ : (D[Φ,hΦ₀]).IsEffectiveCartier) (hN : Module.finrank ℤ N = 2) :
    ∃ (hpre : PrestableFamily (C[Ψ,hΨ₀] ↘ S)) (l : ℕ) (_ : NeZero l),
      letI := hpre
      ∀ q : δ → (C[Ψ,hΨ₀] ↘ S).smoothLocus,
        ∃ U : Scheme.NodalCycleNumbering q l, (β).IsOrientedCycleSubdivision U A := by
  obtain ⟨m, Y, T, e, hT, he, hD, -⟩ := h.exists_toric_subdivision_blowup_tower hΦ hΨ hΦ₀ hN
  let D' := ((D[Φ,hΦ₀]).comap T.toBase).radical
  have : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [algebraicRealization_over]
    exact hN ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have : QuasiCompact (Φ.algebraicRealization ↘ S) := quasiCompact_of_compactSpace _
  have hT' : IsNodalBoundaryTower (D[Φ,hΦ₀]) (Φ.algebraicRealization ↘ S) (𝟙 _) T := by
    simpa only [algebraicRealization_over] using hT
  let : Y.Over S := ⟨T.toBase ≫ Φ.algebraicRealization ↘ S⟩
  let : PrestableFamily (D'.subscheme ↘ S) := by
    rw [over_eq_subschemeι_comp]
    exact hT'.prestableFamily_radical_comap_toBase hD₀
  have : NeZero (n + m) := ⟨by have := NeZero.ne n; omega⟩
  let marks : Empty → (D'.subscheme ↘ S).smoothLocus := Empty.elim
  obtain ⟨W, _, hW⟩ := hT'.exists_isOrientedCycleSubdivision_nodalBoundaryTower hD₀ A marks
  obtain ⟨d, hd⟩ := D'.exists_iso_of_comap_eq_ker e (D[Ψ,hΨ₀]).subschemeι
    (hD.trans (ker_subschemeι _).symm)
  have hY : Y ↘ S = T.toBase ≫ Φ.algebraicRealization ↘ S := rfl
  have : d.hom.IsOver S := ⟨by
    rw [D'.over_eq_subschemeι_comp, reassoc_of% hd, hY, reassoc_of% he, comp_over,
      ← (D[Ψ,hΨ₀]).over_eq_subschemeι_comp]⟩
  have hpre : PrestableFamily (C[Ψ,hΨ₀] ↘ S) := by
    rw [← comp_over d.hom S]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
      d.hom _).2 inferInstance
  have : d.symm.hom.IsOver S := inferInstanceAs (d.inv.IsOver S)
  refine ⟨hpre, n + m, inferInstance, ?_⟩
  intro q
  let U := d.symm.mapNodalCycleNumbering W (q := q)
  have hforward : d.symm.boundaryCycleAction W U = 1 :=
    d.symm.boundaryCycleAction_mapNodalCycleNumbering W
  have hinv := d.symm.boundaryCycleAction_symm W U
  rw [hforward, inv_one] at hinv
  have hact : d.boundaryCycleAction U W = 1 := by simpa only [Iso.symm_symm_eq] using hinv
  have hsign : DihedralGroup.cycleOrientationSign (d.boundaryCycleAction U W) = 1 := by
    simp only [hact, map_one]
  refine ⟨U, ?_⟩
  have hcomp := (d.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one U W hsign).comp hW
  have hβ : d.hom ≫ subschemeMap D' (D[Φ,hΦ₀]) T.toBase
      (le_map_iff_comap_le.mpr (le_radical _)) = β := by
    rw [← cancel_mono (D[Φ,hΦ₀]).subschemeι, Category.assoc, subschemeMap_subschemeι,
      reassoc_of% hd, he, h.boundaryMap_comp_subschemeι]
  exact hβ ▸ hcomp

end TauCeti.Toric.Fan
