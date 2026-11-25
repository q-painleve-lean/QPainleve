/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Prefixing a marked Sarkisov decrease

A resolved preparation may take place on a nodal refinement before a plane-target
decrease is available. The preparation path and the decreasing continuation compose
on the appended nodal tower. The terminal marking still records the same target
projection and its bidegree. The path lifting is the one used in
`exists_comp_sarkisovPath_on_nodalTower`.
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

local notation "S" => Spec (CommRingCat.of ℂ)
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
  {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)] [IsIntegral X] [IsNoetherian X]
  {D : X.IdealSheafData} {A B : LogarithmicProjection i D}
  (hRank : finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
  {m : ℕ} {Y : Scheme} {T : BlowupTower X m Y}
  (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)

local notation "F" => precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hT

private theorem HasPlaneTargetDecrease.of_path_on_append
    {n : ℕ} {W : Scheme} {U : BlowupTower Y n W}
    (hU : IsNodalBoundaryTower total[D,T] (T.toBase ≫ X ↘ S) (𝟙 Y) U)
    {d next : ℕ ×ₗ ℕ} (hlt : next < d) :
    let : Y.Over S := over[T]
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hT]
    let : IsIntegral Y := integral[hT]
    let : IsNoetherian Y := T.isNoetherian
    let : W.Over S := over[U]
    let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hU]
    let : IsIntegral W := integral[hU]
    ∀ {L C R : LogarithmicProjection i total[total[D,T],U]},
      SarkisovPath L C →
      L.fan = A.fan → L.hom ≍ (U.toBase ≫ T.toBase) ≫ A.hom →
      R.fan = B.fan → R.hom ≍ (U.toBase ≫ T.toBase) ≫ B.hom →
      HasPlaneTargetMarking C R next → HasPlaneTargetDecrease A B hRank hD hNode d := by
  intro hY hSmoothY hIntY hNoethY hW hSmoothW hIntW L C R p hL hhL hR hhR hm
  let := hY
  let := hSmoothY
  let := hIntY
  let := hIntW
  let := hNoethY
  let hTU : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) (T.append U) :=
    hT.append (hU.congr (by simp) (by simp))
  -- Transport the path and terminal marking across the two presentations of the top.
  let P (f : W ⟶ X) (s : W ⟶ S) (hs : SmoothOfRelativeDimension 2 s)
      (J : W.IdealSheafData) : Prop :=
    letI : W.Over S := ⟨s⟩
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := hs
    ∃ L' C' R' : LogarithmicProjection i J,
      L'.fan = A.fan ∧ L'.hom ≍ f ≫ A.hom ∧ R'.fan = B.fan ∧ R'.hom ≍ f ≫ B.hom ∧
      Nonempty (SarkisovPath L' C') ∧ HasPlaneTargetMarking C' R' next
  have hbase := toBase_append T U
  have hs : (T.append U).toBase ≫ X ↘ S = U.toBase ≫ Y ↘ S := by
    rw [hbase, Category.assoc]
    rfl
  have hJ : total[D,T.append U] = total[total[D,T],U] := by
    rw [hbase, radical_comap_radical, comap_comp]
  have transport {f g : W ⟶ X} {s t : W ⟶ S}
      {hs : SmoothOfRelativeDimension 2 s} {ht : SmoothOfRelativeDimension 2 t}
      {J K : W.IdealSheafData} (hf : f = g) (hst : s = t) (hJK : J = K) :
      P f s hs J → P g t ht K := by
    subst g t K
    exact id
  have hP := transport hbase.symm hs.symm hJ.symm
    (hs := hSmoothW) (ht := smooth[hTU]) ⟨L, C, R, hL, hhL, hR, hhR, ⟨p⟩, hm⟩
  let : W.Over S := over[T.append U]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hTU]
  obtain ⟨L', C', R', hL', hhL', hR', hhR', ⟨q⟩, hm'⟩ := hP
  let G := precomposeSarkisovOfNodalTower (i := i) hRank hD hNode hTU
  have hsource : obj[G,A] = L' := LogarithmicProjection.ext
    ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hL'.symm)
    ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hhL'.symm)
  have htarget : obj[G,B] = R' := LogarithmicProjection.ext
    ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hR'.symm)
    ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hhR'.symm)
  exact ⟨next, hlt, m + n, W, T.append U, hTU, C', ⟨hsource.symm ▸ q⟩, htarget.symm ▸ hm'⟩

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
    ∀ {M : LogarithmicProjection i total[D,T]} (_ : SarkisovPath (obj[F,A]) M) {d : ℕ ×ₗ ℕ},
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
  have identify (L : LogarithmicProjection i D) :
      (obj[G,obj[F,L]]).fan = L.fan ∧
        (obj[G,obj[F,L]]).hom ≍ (U.toBase ≫ T.toBase) ≫ L.hom := by
    have hfan := precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT L
    have hhom := precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hT L
    refine ⟨(precomposeSarkisovOfNodalTower_obj_fan ..).trans hfan, ?_⟩
    rw [Category.assoc]
    exact (precomposeSarkisovOfNodalTower_obj_hom ..).trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hfan) HEq.rfl hhom)
  exact HasPlaneTargetDecrease.of_path_on_append hRank hD hNode hT hU hlt
    (@Quiver.Path.comp _ sarkisovQuiver _ _ _ (mapPath[G,p]) q)
    (identify A).1 (identify A).2 (identify B).1 (identify B).2 hm

end TauCeti.Toric.Fan.LogarithmicProjection
