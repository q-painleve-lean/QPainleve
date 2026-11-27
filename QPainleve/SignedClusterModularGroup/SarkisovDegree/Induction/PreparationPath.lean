/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary

/-!
# Prefixing a marked Sarkisov decrease

A resolved preparation may take place on a nodal refinement before a plane-target
decrease is available. The preparation path and the decreasing continuation compose
on the appended nodal tower. The terminal marking still records the same target
projection and its bidegree.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "over[" T "]" => OverClass.ofHom ((BlowupTower.toBase T) ≫ _ ↘ S)
local notation "smooth[" h "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)
local notation "integral[" h "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)
local notation "total[" D "," T "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase T))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "mapPath[" F "," p "]" =>
  @Prefunctor.mapPath _ sarkisovQuiver _ sarkisovQuiver F _ _ p

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {X : Scheme} [X.Over (Spec (.of k₀))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k₀))]
    [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData} {A B : LogarithmicProjection k₀ i D}
  (hRank : finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ Spec (.of k₀)))
  {m : ℕ} {Y : Scheme} {T : BlowupTower X m Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k₀)) (𝟙 X) T)

local notation "F" => precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hT

/-- Prefix a marked decreasing continuation by a resolved path on a nodal
refinement. Both paths are resolved on a single appended tower. The terminal
marking is for the pullback of the original target, with the bidegree of the
continuation's new marking. -/
theorem HasPlaneTargetDecrease.of_prefix_on_nodalTower :
    let : Y.Over S := over[T]
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hT]
    let : IsIntegral Y := integral[hT]
    let : IsNoetherian Y := T.isNoetherian
    let hE := hT.radical_comap_toBase hD hNode
    ∀ {M : LogarithmicProjection k₀ i total[D,T]} (_ : SarkisovPath (obj[F,A]) M) {d : ℕ ×ₗ ℕ},
      HasPlaneTargetDecrease M (obj[F,B]) hRank hE.1 hE.2 d →
      HasPlaneTargetDecrease A B hRank hD hNode d := by
  intro hY hSmoothY hIntY hNoethY hE M p d h
  let := hY
  let := hSmoothY
  let := hIntY
  let := hNoethY
  obtain ⟨next, hlt, n, W, U, hU, C, ⟨q⟩, hm⟩ := h
  let : W.Over S := over[U]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hU]
  let : IsIntegral W := integral[hU]
  let G := precomposeSarkisovOfNodalTower (i := i) hRank hE.1 hE.2 hU
  obtain ⟨hL, hhL⟩ := precomposeSarkisovOfNodalTower_obj_comp hRank hD hNode hT hU A
  obtain ⟨hR, hhR⟩ := precomposeSarkisovOfNodalTower_obj_comp hRank hD hNode hT hU B
  obtain ⟨hTU, L', R', hL', hhL', hR', hhR', C', ⟨q'⟩, hm'⟩ :=
    exists_pullback_projections_on_nodalTower_append hT hU
      (fun L R ↦ ∃ C, Nonempty (SarkisovPath L C) ∧ HasPlaneTargetMarking C R next)
      ⟨obj[G,obj[F,A]], obj[G,obj[F,B]], hL, hhL, hR, hhR, C,
        ⟨@Quiver.Path.comp _ sarkisovQuiver _ _ _ (mapPath[G,p]) q⟩, hm⟩
  let : W.Over S := over[T.append U]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hTU]
  let H := precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hTU
  have hsource : obj[H,A] = L' := LogarithmicProjection.ext
    ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hL'.symm)
    ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hhL'.symm)
  have htarget : obj[H,B] = R' := LogarithmicProjection.ext
    ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hR'.symm)
    ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hhR'.symm)
  exact ⟨next, hlt, m + n, W, T.append U, hTU, C', ⟨hsource.symm ▸ q'⟩, htarget.symm ▸ hm'⟩

end TauCeti.Toric.Fan.LogarithmicProjection
