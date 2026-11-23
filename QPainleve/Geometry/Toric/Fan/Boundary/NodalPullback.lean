/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.AlongBoundary
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.Geometry.Toric.Fan.FunctionField
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Nodal projections of toric internal models

The binomial centers lie on the smooth open orbit charts of the reduced toric boundary.
Consequently a nodal blowup tower of the fan surface pulls back to a nodal blowup tower
on each ordered internal model. This gives a nodal projection when comparing internal
models built over a toric subdivision.
-/

public section

open AlgebraicGeometry CategoryTheory Limits QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ : Nonempty Φ.cones]

local notation "D₀" => Φ.boundaryIdeal hΦ
local notation "base" => Φ.algebraicRealizationStructureMap

private theorem not_isNodeAt_mem_support_internalCenter (b : Module.Basis (Fin 2) ℤ N)
    (ρ : Φ.Ray) (c : ℂˣ) {x : (D₀).subscheme}
    (hx : x ∈ (ρ.internalCenter b c).val.support) :
    ¬ ((D₀).subschemeι ≫ base).IsNodeAt x := by
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let χ := (b.detDualEquiv ρ.primitiveGenerator).toAddMonoidHom
  have hχ : χ ρ.primitiveGenerator = 0 := b.detDualEquiv_self _
  let hprim := ρ.surjective_detCharacter b
  let a := ρ.binomialCenterOnBoundary hdim hχ hprim c
  let j := ρ.orbitToBoundary hdim hχ hprim
  have ha : (ρ.internalCenter b c).val = a.ker := Ray.internalCenter_val _ _ _
  have hx' : x ∈ Set.range a := by
    rwa [ha, ← SetLike.mem_coe, Scheme.Hom.support_ker,
      a.isClosedEmbedding.isClosed_range.closure_eq] at hx
  have hxj : x ∈ Set.range j :=
    ρ.range_binomialCenterOnBoundary_subset_range_orbitToBoundary hdim hχ hprim c hx'
  obtain ⟨p, rfl⟩ := hxj
  intro hn
  let f := (D₀).subschemeι ≫ base
  have hsm : SmoothOfRelativeDimension 1 (j ≫ f) :=
    ρ.smoothOfRelativeDimension_orbitToBoundary hdim hχ hprim
  have hn' := (f.isNodeAt_comp_iff_of_isOpenImmersion j p).mpr hn
  let : Smooth (j ≫ f) := hsm.smooth
  apply (j ≫ f).not_isNodeAt_of_mem_smoothLocus _ hn'
  rw [(j ≫ f).smoothLocus_eq_top]
  trivial

/-- A nodal blowup tower of the toric boundary pulls back to a nodal tower of the
strict boundary of the ordered internal model, with the same number of nodal blowups.
The comparison allows repeated binomial centers, and gives a cartesian square over
the original fan scheme. -/
theorem exists_isPullback_nodalBoundaryTower_internalBlowupTower
    {n m : ℕ} {Y : Scheme} {T : BlowupTower Φ.algebraicRealization n Y}
    (hT : IsNodalBoundaryTower (D₀) base (𝟙 _) T)
    (b : Module.Basis (Fin 2) ℤ N) (ρ : Fin m → Φ.Ray) (c : Fin m → ℂˣ) :
    let U := internalBlowupTower b ρ c
    ∃ (Z : Scheme) (R : BlowupTower U.1 n Z) (g : Z ⟶ Y),
      IsNodalBoundaryTower U.2.boundaryι.ker (U.2.toTower.toBase ≫ base) (𝟙 U.1) R ∧
      IsPullback g R.toBase T.toBase U.2.toTower.toBase := by
  have hD : IsReduced (D₀).subscheme := by
    rw [Fan.boundaryIdeal_def]
    infer_instance
  have hb : IsNodalBoundaryTower (D₀).subschemeι.ker base (𝟙 _) T := by
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hT
  dsimp only
  rw [internalBlowupTower_eq_alongBoundary]
  exact IsNodalBoundaryTower.exists_isPullback_alongBoundary_of_avoids_nodes
    (D₀).subschemeι hb _ (fun j _ hp ↦ not_isNodeAt_mem_support_internalCenter b (ρ j) (c j) hp)

end TauCeti.Toric.Fan
