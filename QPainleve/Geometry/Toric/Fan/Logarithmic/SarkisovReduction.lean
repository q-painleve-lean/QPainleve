/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.ProjectiveSpace.Plane
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Logarithmic.CommonResolution
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower

/-!
# Plane reduction of resolved Sarkisov factorizations

Both ends of a specified toric change of presentation can be reduced to the
projective plane on one nodal blowup tower. A resolved factorization between
the plane projections then extends to the original projections.

This is the reduction to a plane target in [Lutz, Theorem 8.4][HKL].
The construction uses `exists_common_nodal_resolution_of_toric_changes`
and concatenates the paths of regular partial composites.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

variable {Z : Scheme} [Z.Over S] [IsIntegral Z] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData}

private theorem exists_star_path_to_coarsening
    (A : LogarithmicProjection i D) (hN : Module.finrank ℤ N = 2)
    {Ω Ψ : Fan i} (J : Ω.IsSubdivision A.fan) (K : Ω.IsSubdivision Ψ)
    (hΩ : Ω.IsRegular) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
    (g : Z ⟶ X[Ω]) (he : g ≫ π[J] = A.hom)
    (h : letI := hcΨ.nonempty_cones
      ∃ hOver : (g ≫ π[K]) ≫ Fan.algebraicRealizationStructureMap Ψ = Z ↘ S,
        letI : (g ≫ π[K]).IsOver S := ⟨hOver⟩
        letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
        IsModification (g ≫ π[K]) ∧
          (Ψ.boundaryIdeal inferInstance).comap (g ≫ π[K]) =
            D * ramificationIdealSheaf ℂ (g ≫ π[K])) :
    ∃ C : LogarithmicProjection i D,
      C.fan = Ψ ∧ IsModification C.hom ∧ Nonempty (Quiver.Path A C) := by
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  let : Nonempty Ω.cones := J.nonempty_cones_of_nonempty A.isComplete.nonempty_cones
  obtain ⟨hOver, hMod, hpole⟩ := h
  let : (g ≫ π[K]).IsOver S := ⟨hOver⟩
  let : IsModification (g ≫ π[K]) := hMod
  let C : LogarithmicProjection i D :=
    ⟨Ψ, hΨ, hcΨ, g ≫ π[K], inferInstance, inferInstance, hpole⟩
  let : IsModification π[J] :=
    J.isModification_algebraicMap A.isRegular hΩ A.isComplete.nonempty_cones hN
  let : IsDominant (g ≫ π[J]) := he.symm ▸ A.isDominant
  let : IsDominant g := IsModification.isDominant_of_comp g π[J]
  obtain ⟨p, -, -⟩ :=
    exists_resolved_toric_star_factorization A C hN hΩ J K g he (rfl : g ≫ π[K] = C.hom)
  exact ⟨C, rfl, hMod, ⟨p⟩⟩

/-- To factor the specified change of presentation between arbitrary complete
regular rank-two toric targets, it suffices to factor the changes between
projective plane targets. Both plane projections lie on one nodal refinement
and are modifications. Any further nodal refinement used by the plane
factorization carries both end paths and the middle path. -/
theorem exists_resolved_sarkisov_factorization_of_plane
    (b : Module.Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hPlane : ∀ {Y : Scheme} [Y.Over S] [IsIntegral Y] [Y.IsProjectiveOver ℂ]
      [SmoothOfRelativeDimension 2 (Y ↘ S)] {R : Y.IdealSheafData},
      letI : IsNoetherian Y := isNoetherian_of_finiteType (Y ↘ S)
      R.IsEffectiveCartier →
      AtWorstNodalOfRelativeDimensionOne (R.subschemeι ≫ Y ↘ S) →
      ∀ (C E : LogarithmicProjection i R) [IsModification C.hom] [IsModification E.hom],
        C.fan = projectiveSpace b hi → E.fan = projectiveSpace b hi →
        HasResolvedSarkisovFactorization C E)
    [Z.IsProjectiveOver ℂ] (A B : LogarithmicProjection i D)
    [IsModification A.hom] [IsModification B.hom] (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S)) :
    letI : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
    HasResolvedSarkisovFactorization A B := by
  let : IsNoetherian Z := isNoetherian_of_finiteType (Z ↘ S)
  let plane := projectiveSpace b hi
  let hplane := isRegular_projectiveSpace b hi
  let hcplane := isComplete_projectiveSpace b hi
  let : Nonempty plane.cones := hcplane.nonempty_cones
  let hRank := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let L : Bool → LogarithmicProjection i D := fun j ↦ cond j B A
  let : ∀ j, IsModification (L j).hom := by
    intro j
    cases j <;> assumption
  let : ∀ j, (L j).hom.IsOver S := fun j ↦ (L j).isOver
  obtain ⟨n, Y, T, hT, h⟩ := exists_common_nodal_resolution_of_toric_changes
    (fun _ : Bool ↦ b) (fun j ↦ (L j).isRegular) (fun j ↦ (L j).isComplete)
    (fun _ ↦ hplane) (fun _ ↦ hcplane) (fun j ↦ (L j).hom) hD hNode
    (fun j ↦ (L j).comap_boundaryIdeal)
  let : Y.Over S := ⟨T.toBase ≫ Z ↘ S⟩
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (Z ↘ S)
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  have hPole := hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode
    (Iso.refl Y) T.toBase (Category.id_comp _)
  let L' (j : Bool) := precomposeProjection hRank T.toBase hPole (L j)
  have hPath (j : Bool) : ∃ C : LogarithmicProjection i (D.comap T.toBase).radical,
      C.fan = plane ∧ IsModification C.hom ∧ Nonempty (Quiver.Path (L' j) C) := by
    obtain ⟨Ω, J, K, g, hΩ, -, -, he, hq⟩ := h j
    exact exists_star_path_to_coarsening (L' j) hRank J K hΩ hplane hcplane g he ((hq plane K).2.imp
      fun _ hm ↦ hm hplane)
  obtain ⟨C, hC, hModC, ⟨p⟩⟩ := hPath false
  obtain ⟨E, hE, hModE, ⟨q⟩⟩ := hPath true
  let : IsModification C.hom := hModC
  let : IsModification E.hom := hModE
  obtain ⟨hR, hNodeR⟩ := hT.radical_comap_toBase hD hNode
  exact hasResolvedSarkisovFactorization_of_star_paths A B hRank hD hNode hT
    rfl HEq.rfl rfl HEq.rfl p q (hPlane hR hNodeR C E hC hE)

end TauCeti.Toric.Fan.LogarithmicProjection
