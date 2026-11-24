/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Logarithmic.Centres
public import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint
public import QPainleve.Geometry.Toric.Fan.Smooth

import QPainleve.Geometry.Toric.Fan.Boundary.Node

/-!
# Projected centers of logarithmic toric resolutions

Each projected center of a point resolution of a toric surface with no zeros in the
pulled-back logarithmic form is on the toric boundary. At a node it is the distinguished
point of a unique two-ray cone. At a smooth boundary point its ideal is given by a
unique ray and binomial parameter. These are the two kinds of proper centers used in
Lutz's Sarkisov links in [the appendix to Hacking and Keating, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N)

local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "X" => Φ.algebraicRealization
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "f" => Φ.algebraicRealizationStructureMap

/-- A projected center of a specified logarithmic point tower on a complete regular
toric surface is either a toric node or a smooth binomial center. The node determines
a unique two-ray cone, and the smooth center determines a unique ray and parameter.
The assertion concerns the reduced ideal on the original surface and allows projected
images of infinitely near centers. -/
theorem baseCenter_cases_of_totalTransform_le_ramification
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {Y : Scheme} {n : ℕ}
    {T : QPainleve.BlowupTower X n Y} (hT : QPainleve.BlowupTower.IsClosedPointTower X T) :
    letI := hc.nonempty_cones
    letI : SmoothOfRelativeDimension 2 (X ↘ S) :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let D := Φ.boundaryIdeal hc.nonempty_cones
    D.comap T.toBase ≤ hT.ramificationIdealSheafToBase ℂ →
    ∀ j : Fin n, let p := hT.baseCenter j
      (∃! σ : Φ.cones, Nat.card (ToricRay σ.val) = 2 ∧
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) = p) ∨
      (¬ D.IsNodeOfReducedBoundary f p ∧
        ∃! a : Φ.Ray × ℂˣ, (a.1.internalCenter b a.2).val.map D.subschemeι =
          (Scheme.fromSpecResidueField X p).ker) := by
  intro D h j p
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 (X ↘ S) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  have hp : IsClosed ({p} : Set X) := hT.isClosed_baseCenter j
  have hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc rankTwo
  have hmem : p ∈ D.support :=
    hT.range_baseCenter_subset_support_of_totalTransform_le_ramification ℂ hD h ⟨j, rfl⟩
  by_cases hn : D.IsNodeOfReducedBoundary f p
  · exact Or.inl ((Φ.isNodeOfReducedBoundary_iff_existsUnique_twoRayCone hΦ hc rankTwo).mp hn)
  · exact Or.inr
      ⟨hn, Φ.existsUnique_internalCenter_of_mem_boundary_of_not_isNode b hΦ hc hp hmem hn⟩

end TauCeti.Toric.Fan
