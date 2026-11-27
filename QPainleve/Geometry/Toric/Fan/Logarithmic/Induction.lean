/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import TauCeti.AlgebraicGeometry.Noetherian

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Induction for resolved Sarkisov paths

A decreasing block and its continuation can be resolved on successive nodal
blowup towers. Pulling the earlier block to the top of the continuation gives
one path whose partial composites are regular and carry the reduced total pole
boundary. This lets a lexicographic decrease in Sarkisov bidegree produce a
finite factorization on one resolution, as in the proof of
[Lutz's Theorem 8.4][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

open scoped Sarkisov

variable {K : Type} [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of K)
local notation "over[" T "]" => OverClass.ofHom ((BlowupTower.toBase T) ≫ _ ↘ S)
local notation "smooth[" hT "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower hT) (_ ↘ S)
local notation "integral[" hT "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower hT) (_ ↘ S)

variable {Z : Scheme} [Z.Over (Spec (.of K))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of K))]
  [IsIntegral Z] [IsNoetherian Z] {D : Z.IdealSheafData}

local notation "Total[" D "," T "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase T))

/-- Lift a resolved Sarkisov path along a nodal blowup tower by taking the
reduced total boundary as the pole ideal. The fan and rational map of each
link are unchanged. -/
def precomposeSarkisovOfNodalTower (hRank : Module.finrank ℤ N = 2)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ Spec (.of K)))
    {n : ℕ} {W : Scheme} {T : BlowupTower Z n W}
    (hT : IsNodalBoundaryTower D (Z ↘ Spec (.of K)) (𝟙 Z) T) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    @Prefunctor (LogarithmicProjection K i D) sarkisovQuiver
      (LogarithmicProjection K i Total[D,T]) sarkisovQuiver := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  exact precomposeSarkisov (k := K) hRank T.toBase
    (hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode (Iso.refl W) T.toBase
      (Category.id_comp _))

variable (hRank : Module.finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ Spec (.of K)))
  {n : ℕ} {W : Scheme} {T : BlowupTower Z n W}
  (hT : IsNodalBoundaryTower D (Z ↘ Spec (.of K)) (𝟙 Z) T)

local notation "lift[" h "]" => precomposeSarkisovOfNodalTower (K := K) (i := i) hRank hD hNode h
-- The same vertices carry both the star and the Sarkisov quivers.
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "mapPath[" F "," p "]" =>
  @Prefunctor.mapPath _ sarkisovQuiver _ sarkisovQuiver F _ _ p

/-- Refining the resolving surface preserves the target fan. -/
@[simp]
theorem precomposeSarkisovOfNodalTower_obj_fan (A : LogarithmicProjection K i D) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    (obj[lift[hT],A]).fan = A.fan := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  unfold precomposeSarkisovOfNodalTower
  exact precomposeSarkisov_obj_fan ..

/-- A vertex on the refined resolution is the original projection precomposed
with the tower morphism. -/
theorem precomposeSarkisovOfNodalTower_obj_hom (A : LogarithmicProjection K i D) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    (obj[lift[hT],A]).hom ≍ T.toBase ≫ A.hom := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  unfold precomposeSarkisovOfNodalTower
  exact precomposeSarkisov_obj_hom ..

/-- Two successive nodal lifts preserve the original fan and precompose the
original projection with the composite tower morphism. -/
theorem precomposeSarkisovOfNodalTower_obj_comp {m : ℕ} {Y : Scheme} {U : BlowupTower W m Y}
    (hU : IsNodalBoundaryTower Total[D,T] (T.toBase ≫ Z ↘ S) (𝟙 W) U)
    (A : LogarithmicProjection K i D) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    letI : IsNoetherian W := T.isNoetherian
    letI : Y.Over S := over[U]
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
    letI : IsIntegral Y := integral[hU]
    let hE := hT.radical_comap_toBase hD hNode
    let F := precomposeSarkisovOfNodalTower (K := K) (i := i) hRank hE.1 hE.2 hU
    (obj[F,obj[lift[hT],A]]).fan = A.fan ∧
      (obj[F,obj[lift[hT],A]]).hom ≍ (U.toBase ≫ T.toBase) ≫ A.hom := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : IsNoetherian W := T.isNoetherian
  let : Y.Over S := over[U]
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
  let : IsIntegral Y := integral[hU]
  have hfan := precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT A
  have hhom := precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hT A
  refine ⟨(precomposeSarkisovOfNodalTower_obj_fan ..).trans hfan, ?_⟩
  rw [Category.assoc]
  exact (precomposeSarkisovOfNodalTower_obj_hom ..).trans
    (heq_comp rfl rfl (congrArg (Fan.finiteFanScheme K) hfan) HEq.rfl hhom)

variable {A B : LogarithmicProjection K i D}

/-- Transport two lifted projections and a predicate on them from successive
nodal refinements to their appended tower. The predicate can record a path
and any additional marking on the refined resolution. -/
theorem exists_pullback_projections_on_nodalTower_append
    {m : ℕ} {Y : Scheme} {U : BlowupTower W m Y}
    (hU : IsNodalBoundaryTower Total[D,T] (T.toBase ≫ Z ↘ S) (𝟙 W) U)
    (P : ∀ [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [PreirreducibleSpace Y]
      {J : Y.IdealSheafData}, LogarithmicProjection K i J → LogarithmicProjection K i J → Prop) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    letI : IsNoetherian W := T.isNoetherian
    letI : Y.Over S := over[U]
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
    letI : IsIntegral Y := integral[hU]
    (∃ A' B' : LogarithmicProjection K i Total[Total[D,T],U],
      A'.fan = A.fan ∧ A'.hom ≍ (U.toBase ≫ T.toBase) ≫ A.hom ∧
      B'.fan = B.fan ∧ B'.hom ≍ (U.toBase ≫ T.toBase) ≫ B.hom ∧ P A' B') →
    ∃ hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U),
      letI : Y.Over S := over[T.append U]
      letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hTU]
      letI : IsIntegral Y := integral[hTU]
      ∃ A' B' : LogarithmicProjection K i Total[D,T.append U],
        A'.fan = A.fan ∧ A'.hom ≍ (T.append U).toBase ≫ A.hom ∧
        B'.fan = B.fan ∧ B'.hom ≍ (T.append U).toBase ≫ B.hom ∧ P A' B' := by
  intro h
  have hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U) :=
    hT.append (hU.congr (by simp) (by simp))
  have hbase := toBase_append T U
  have hs : (T.append U).toBase ≫ Z ↘ S = U.toBase ≫ T.toBase ≫ Z ↘ S := by
    rw [hbase, Category.assoc]
  have hJ : Total[D,T.append U] = Total[Total[D,T],U] := by
    rw [hbase, radical_comap_radical, comap_comp]
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : IsNoetherian W := T.isNoetherian
  let : IsIntegral Y := integral[hU]
  let Q (f : Y ⟶ Z) (s : Y ⟶ S) (hs : SmoothOfRelativeDimension 2 s)
      (J : Y.IdealSheafData) : Prop :=
    letI : Y.Over S := ⟨s⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hs
    ∃ A' B' : LogarithmicProjection K i J,
      A'.fan = A.fan ∧ A'.hom ≍ f ≫ A.hom ∧ B'.fan = B.fan ∧ B'.hom ≍ f ≫ B.hom ∧ P A' B'
  refine ⟨hTU, ?_⟩
  have transport {f g : Y ⟶ Z} {s t : Y ⟶ S}
      {hs : SmoothOfRelativeDimension 2 s} {ht : SmoothOfRelativeDimension 2 t}
      {J K : Y.IdealSheafData} (hfg : f = g) (hst : s = t) (hJK : J = K) :
      Q f s hs J → Q g t ht K := by
    subst g t K
    exact id
  exact transport hbase.symm hs.symm hJ.symm h

/-- Concatenate a path on the top of a nodal tower with a continuation on a
further nodal tower. The result lives on the appended tower, with the original
source projection and the continuation's final projection pulled back to its top. -/
theorem exists_comp_sarkisovPath_on_nodalTower {m : ℕ} {Y : Scheme} {U : BlowupTower W m Y}
    (hU : IsNodalBoundaryTower Total[D,T] (T.toBase ≫ Z ↘ S) (𝟙 W) U) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    letI : IsNoetherian W := T.isNoetherian
    letI : Y.Over S := over[U]
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
    letI : IsIntegral Y := integral[hU]
    ∀ {C : LogarithmicProjection K i Total[D,T]}
      (_ : SarkisovPath (obj[lift[hT],A]) C)
      {A' B' : LogarithmicProjection K i Total[Total[D,T],U]}
      (_ : SarkisovPath A' B'),
      A'.fan = C.fan → A'.hom ≍ U.toBase ≫ C.hom →
      B'.fan = B.fan → B'.hom ≍ U.toBase ≫ T.toBase ≫ B.hom →
      ∃ hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U),
        letI : Y.Over S := over[T.append U]
        letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hTU]
        letI : IsIntegral Y := integral[hTU]
        ∃ A'' B'' : LogarithmicProjection K i Total[D,T.append U],
          A''.fan = A.fan ∧ A''.hom ≍ (T.append U).toBase ≫ A.hom ∧
          B''.fan = B.fan ∧ B''.hom ≍ (T.append U).toBase ≫ B.hom ∧
          Nonempty (SarkisovPath A'' B'') := by
  intro C p A' B' q hA' hAh hB' hBh
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : IsNoetherian W := T.isNoetherian
  let : Y.Over S := over[U]
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
  let : IsIntegral Y := integral[hU]
  obtain ⟨hE, hENode⟩ := hT.radical_comap_toBase hD hNode
  let F := precomposeSarkisovOfNodalTower (K := K) (i := i) hRank hE hENode hU
  have hC : obj[F,C] = A' :=
    LogarithmicProjection.ext
      ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hA'.symm)
      ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hAh.symm)
  obtain ⟨hAf, hAh'⟩ := precomposeSarkisovOfNodalTower_obj_comp hRank hD hNode hT hU A
  exact exists_pullback_projections_on_nodalTower_append hT hU
    (fun L R ↦ Nonempty (SarkisovPath L R))
    ⟨obj[F,obj[lift[hT],A]], B', hAf, hAh', hB', by simpa only [Category.assoc] using hBh,
      ⟨@Quiver.Path.comp _ sarkisovQuiver _ _ _ (hC ▸ mapPath[F,p]) q⟩⟩

include hD hNode hRank in
private theorem hasPathOver_of_path (p : SarkisovPath A B) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    ∃ A' B' : LogarithmicProjection K i Total[D,T],
      A'.fan = A.fan ∧ A'.hom ≍ T.toBase ≫ A.hom ∧
      B'.fan = B.fan ∧ B'.hom ≍ T.toBase ≫ B.hom ∧ Nonempty (SarkisovPath A' B') := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let F := lift[hT]
  let A' : LogarithmicProjection K i Total[D,T] := obj[F,A]
  let B' : LogarithmicProjection K i Total[D,T] := obj[F,B]
  exact ⟨A', B',
    precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT A,
    precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hT A,
    precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT B,
    precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hT B,
    ⟨mapPath[F,p]⟩⟩

include hD hNode in
/-- A terminal path or a strictly decreasing resolved block at every admissible
pair of projections gives a finite path on one nodal refinement of the initial
surface. Admissibility can record the plane or Hirzebruch marking used to compute
the bidegree. At a decreasing block, the target projection is pulled back to the
new resolving surface, so the induction continues toward the same target. -/
theorem exists_sarkisov_path_of_bidegree_decrease
    (P : ∀ {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
      {E : X.IdealSheafData},
      LogarithmicProjection K i E → LogarithmicProjection K i E → ℕ ×ₗ ℕ → Prop)
    (step : ∀ {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
      [IsIntegral X] [IsNoetherian X] {E : X.IdealSheafData}
      (C F : LogarithmicProjection K i E) (bidegree : ℕ ×ₗ ℕ)
      (hE : E.IsEffectiveCartier)
      (hENode : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ X ↘ S)),
      P C F bidegree →
      Nonempty (SarkisovPath C F) ∨
        ∃ (next : ℕ ×ₗ ℕ) (_ : next < bidegree)
          (k : ℕ) (Y : Scheme) (U : BlowupTower X k Y)
          (hU : IsNodalBoundaryTower E (X ↘ S) (𝟙 X) U),
          letI : Y.Over S := over[U]
          letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
          letI : IsIntegral Y := integral[hU]
          let lift := precomposeSarkisovOfNodalTower (K := K) (i := i) hRank hE hENode hU
          ∃ C' : LogarithmicProjection K i Total[E,U],
            Nonempty (SarkisovPath (obj[lift,C]) C') ∧ P C' (obj[lift,F]) next)
    (bidegree : ℕ ×ₗ ℕ) (hP : P A B bidegree) :
    ∃ (k : ℕ) (Y : Scheme) (U : BlowupTower Z k Y)
      (hU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) U),
      letI : Y.Over S := over[U]
      letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
      letI : IsIntegral Y := integral[hU]
      ∃ A' B' : LogarithmicProjection K i Total[D,U],
        A'.fan = A.fan ∧ A'.hom ≍ U.toBase ≫ A.hom ∧
        B'.fan = B.fan ∧ B'.hom ≍ U.toBase ≫ B.hom ∧ Nonempty (SarkisovPath A' B') := by
  induction bidegree using (wellFounded_lt (α := ℕ ×ₗ ℕ)).induction generalizing Z with
  | h bidegree ih =>
    rcases step A B bidegree hD hNode hP with hp | hstep
    · obtain ⟨p⟩ := hp
      let hnil : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (.nil : BlowupTower Z 0 Z) := .nil
      exact ⟨0, Z, .nil, hnil, hasPathOver_of_path hRank hD hNode hnil p⟩
    · obtain ⟨next, hlt, k, Y, U, hU, C', ⟨p⟩, hP'⟩ := hstep
      let : Y.Over S := over[U]
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
      let : IsIntegral Y := integral[hU]
      let : IsNoetherian Y := U.isNoetherian
      obtain ⟨hE, hENode⟩ := hU.radical_comap_toBase hD hNode
      obtain ⟨l, W, T, hT, A', B', hA', hAh, hB', hBh, ⟨q⟩⟩ :=
        ih next hlt hE hENode hP'
      let : W.Over S := over[T]
      let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
      let : IsIntegral W := integral[hT]
      have hBhom : B'.hom ≍ T.toBase ≫ U.toBase ≫ B.hom := by
        have h := precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hU B
        have hf := precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hU B
        exact hBh.trans (heq_comp rfl rfl (congrArg (Fan.finiteFanScheme K) hf) HEq.rfl h)
      obtain ⟨hUT, hpath⟩ := exists_comp_sarkisovPath_on_nodalTower hRank hD hNode hU hT p q
        hA' hAh (hB'.trans (precomposeSarkisovOfNodalTower_obj_fan ..)) hBhom
      exact ⟨k + l, W, U.append T, hUT, hpath⟩

end TauCeti.Toric.Fan.LogarithmicProjection
