/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Iteration

import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Exit
import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Initial

/-!
# Sarkisov decrease through positive-section preparation

When the high base orders form a nonempty set over open orbits of invariant
fibers, the positive-section pivots and the prepared quadric exit give one
decreasing block for the specified plane map. All vertices are resolved on
one nodal refinement of the original source.

The positive-section descent treats the high-fiber case of
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData
open scoped Sarkisov

namespace TauCeti.Toric.Fan.LogarithmicProjection

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "f[" A "]" => Fan.algebraicRealization (LogarithmicProjection.fan A) ↘ S
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)] [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  {b' : Basis (Fin 2) ℤ N} {hi : IsIntegralLattice i} {e n : ℕ}

private theorem PositiveSectionMarking.exists_sarkisov_step
    {M : HirzebruchPlaneResolution A B b' hi e n}
    {ι : Type} [Fintype ι] [Nonempty ι] (s : PositiveSectionMarking M ι)
    (hD : D.IsEffectiveCartier) (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hbound : 2 * (s.remainingCoefficient - ∑ a, M.order (s.index a)) <
      (2 - (Fintype.card ι : ℤ)) * M.fiberDegree) :
    HasPlaneTargetDecrease A B rankTwo[M.basis] hD hNode
      (hirzebruchSarkisovBidegree M.fiberDegree.toNat 0) := by
  obtain ⟨C, m, W, u, ⟨p⟩, -, hdegree, hcoef, horder⟩ :=
    exists_marked_quadric_of_positive_section_pivots M s
  have hsum : (∑ a, M.order (s.index a)) ≤ ∑ a, W.order (u.index a) :=
    Finset.sum_le_sum fun a _ ↦ horder a
  have hbound' : 2 * (W.fiberCoefficient - ∑ a, W.order (u.index a)) <
      (2 - (Fintype.card ι : ℤ)) * W.fiberDegree := by
    rw [hcoef, hdegree]
    omega
  let : Nonempty C.fan.cones := C.isComplete.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[C] := by
    rw [← rankTwo[W.basis], Fan.algebraicRealization_over]
    exact C.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap C.isRegular
  let : Smooth f[C] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian C.fan.algebraicRealization := isNoetherian_of_finiteType f[C]
  have hexit := exists_sarkisov_step_of_prepared_quadric_ruling_values W.rays W.rays_eq
    W.closed W.planeMap hD hNode W.target_fan W.iso W.source_hom W.target_hom
    W.planeMap_over W.planeMap_birational u.fiber u.index u.first
    (by simpa only [W.ruling_def] using u.ruling_eq) 0
  simp only [← W.lineClass_def, ← W.order_def, ← W.sectionCenters_def] at hexit
  specialize hexit u.off_section (by simpa only [W.fiberDegree_def, W.fiberCoefficient_def,
    Int.natCast_zero]
    using hbound')
  -- The quadric exit supplies the refinement on which to resolve the preparation path.
  obtain ⟨next, hlt, l, Y, T, hT, E, ⟨q⟩, hmark⟩ := hexit
  have hlt' : next < hirzebruchSarkisovBidegree W.fiberDegree.toNat 0 := by
    simpa only [W.fiberDegree_def, Int.natCast_zero] using hlt
  rw [hdegree] at hlt'
  let : Y.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (X ↘ S)
  let F := precomposeSarkisovOfNodalTower (i := i) rankTwo[M.basis] hD hNode hT
  exact ⟨next, hlt', l, Y, T, hT, E,
    ⟨@Quiver.Path.comp _ sarkisovQuiver _ _ _ (@Prefunctor.mapPath _ sarkisovQuiver _
      sarkisovQuiver F _ _ p) q⟩, hmark⟩

/-- A marked resolution with at least one high order admits a strictly decreasing
Sarkisov block if all high orders are over open orbits of invariant fibers.
The block preserves the plane projection and decreases the primary degree
relative to the original ruling degree. -/
theorem HirzebruchPlaneResolution.exists_sarkisov_step_of_high_fibers
    (M : HirzebruchPlaneResolution A B b' hi e n)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S)) :
    let high := Finset.univ.filter (fun j ↦ M.fiberDegree < 2 * M.order j)
    high.Nonempty →
    (∀ j ∈ high, ∃ t : Fin 2, ∃ c : ℂˣ,
      M.closed.baseCenter j = center[M.basis,M.rays ((![1, 3] : Fin 2 → Fin 4) t),c]) →
    HasPlaneTargetDecrease A B rankTwo[M.basis] hD hNode
      (hirzebruchSarkisovBidegree M.fiberDegree.toNat 0) := by
  intro high hhigh hcenters
  let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
  let : SmoothOfRelativeDimension 2 f[A] := by
    rw [← rankTwo[M.basis], Fan.algebraicRealization_over]
    exact A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
  let : Smooth f[A] := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian A.fan.algebraicRealization := isNoetherian_of_finiteType f[A]
  have hinit := exists_positiveSection_selection_of_marked_high_fibers M.rays M.rays_eq
    M.closed M.planeMap M.target_fan M.iso M.source_hom M.target_hom
    M.planeMap_over M.planeMap_birational
  simp only [high, M.fiberDegree_def, M.order_def, M.lineClass_def] at hhigh hcenters
  obtain ⟨-, ⟨fiber, hmarks⟩, selected, hselect, hcard, hbound⟩ := hinit hhigh hcenters
  simp only [← M.lineClass_def, ← M.order_def, ← M.sectionCenters_def] at hselect
  have hpositive : M.sectionCenters.filter (fun j ↦ 0 < M.order j) = M.positiveCenters := by
    ext j
    simp
  rw [hpositive] at hselect
  let s : PositiveSectionMarking M _ :=
    ⟨selected, hselect, hcard, fiber, Subtype.val, fun j ↦ (hmarks j).2.1,
      fun j ↦ by simpa only [M.ruling_def] using (hmarks j).2.2.1,
      fun j ↦ by simpa only [M.sectionCenters_def] using (hmarks j).2.2.2⟩
  let := hhigh.to_subtype
  apply s.exists_sarkisov_step hD hNode
  simpa only [s, PositiveSectionMarking.remainingCoefficient_def, M.fiberDegree_def,
    M.fiberCoefficient_def, M.order_def, M.lineClass_def] using hbound

end TauCeti.Toric.Fan.LogarithmicProjection
