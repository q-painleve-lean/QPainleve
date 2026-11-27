/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Genus
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Iso

/-!
# Normalized boundary genera of toric presentations

Internal blowups preserve the toric boundary as a curve, and blowing up a
boundary node preserves the normalized strict components. Thus a toric
presentation supplies the genus-zero normalization needed to use boundary
periods on the original pair. The comparison uses the fixed boundary embedding
of `WithBoundary` and the genus labels of `Scheme.dualGraphIsoOfIso`.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over (Spec (.of K))] [IsIntegral X] [QuasiCompact (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of K))]

local notation "S" => Spec (CommRingCat.of K)

/-- Every normalized component of a nodal Cartier boundary with a toric
presentation has genus zero, including for an irreducible nodal boundary. -/
theorem HasToricPresentation.genus_blowupComponent_eq_zero
    (h : D.HasToricPresentation (X ↘ S) b i) (hD : D.IsEffectiveCartier)
    (v : irreducibleComponents (D.subscheme.singularLocus K).blowup) :
    (D.subscheme.blowupComponent v).toScheme.genus K = 0 := by
  obtain ⟨m, ⟨Φ, hΦ, hc, rays, c, n, Y, T, hT, e, he, hB⟩⟩ := (hasToricPresentation_iff ..).mp h
  let := hc.nonempty_cones
  let B := Φ.toricBoundaryIdeal K hc.nonempty_cones
  let A := Fan.internalBlowupTower K b rays c
  let R := (D.comap T.toBase).radical
  let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : PrestableFamily (R.subscheme ↘ S) := by
    rw [R.over_eq_subschemeι_comp]
    exact hT.prestableFamily_radical_comap_toBase hD
  let : (Φ.finiteFanScheme K).IsProjectiveOver K :=
    Φ.isProjectiveOver_finiteFanScheme_of_isComplete K hΦ hc b
  let : IsProper (Φ.finiteFanSchemeToSpec K) := by
    rw [← (Φ.finiteFanScheme_over K)]
    infer_instance
  have hrank : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : PrestableFamily (B.subscheme ↘ S) := Φ.prestableFamily_boundary K hΦ hc hrank
  obtain ⟨d, hd⟩ := R.exists_iso_of_comap_eq_ker e A.2.boundaryι hB
  have hY : Y ↘ S = T.toBase ≫ X ↘ S := rfl
  have hover : d.hom ≫ R.subscheme ↘ S = B.subscheme ↘ S := by
    rw [R.over_eq_subschemeι_comp, B.over_eq_subschemeι_comp, (Φ.finiteFanScheme_over K), hY,
      reassoc_of% hd, he, WithBoundary.boundaryι_toBase_assoc]
  let p : PEmpty.{1} → (B.subscheme ↘ S).smoothLocus := PEmpty.elim
  let q : PEmpty.{1} → (R.subscheme ↘ S).smoothLocus := PEmpty.elim
  let a := Scheme.dualGraphIsoOfIso d hover p q (fun j ↦ j.elim)
  refine (hT.forall_genus_blowupComponent_radical_comap_toBase_eq_zero_iff hD).mp ?_ v
  intro w
  obtain ⟨j, hj⟩ := a.vertexEquiv.surjective ((R.subscheme.dualGraphVertexEquiv q).symm w)
  have hgenus := a.genus_vertexEquiv j
  rw [Scheme.dualGraph_genus, hj, Equiv.apply_symm_apply, Scheme.dualGraph_genus] at hgenus
  exact hgenus.trans (Φ.boundaryNormalizationComponent_genus_eq_zero K hΦ b _)

end AlgebraicGeometry.Scheme.IdealSheafData
