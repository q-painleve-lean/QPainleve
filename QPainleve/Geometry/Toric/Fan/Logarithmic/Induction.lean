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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "over[" T "]" => OverClass.ofHom ((BlowupTower.toBase T) ≫ _ ↘ S)
local notation "smooth[" hT "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower hT) (_ ↘ S)
local notation "integral[" hT "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower hT) (_ ↘ S)

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  [IsIntegral Z] [IsNoetherian Z] {D : Z.IdealSheafData}

local notation "Total[" D "," T "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase T))

/-- Lift a resolved Sarkisov path along a nodal blowup tower by taking the
reduced total boundary as the pole ideal. The fan and rational map of each
link are unchanged. -/
def precomposeSarkisovOfNodalTower (hRank : Module.finrank ℤ N = 2)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S))
    {n : ℕ} {W : Scheme} {T : BlowupTower Z n W}
    (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    @Prefunctor (LogarithmicProjection i D) sarkisovQuiver
      (LogarithmicProjection i Total[D,T]) sarkisovQuiver := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  exact precomposeSarkisov hRank T.toBase
    (hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode (Iso.refl W) T.toBase
      (Category.id_comp _))

variable (hRank : Module.finrank ℤ N = 2) (hD : D.IsEffectiveCartier)
  (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S))
  {n : ℕ} {W : Scheme} {T : BlowupTower Z n W}
  (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T)

local notation "lift[" h "]" => precomposeSarkisovOfNodalTower (i := i) hRank hD hNode h
-- The same vertices carry both the star and the Sarkisov quivers.
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "mapPath[" F "," p "]" =>
  @Prefunctor.mapPath _ sarkisovQuiver _ sarkisovQuiver F _ _ p

/-- Refining the resolving surface preserves the target fan. -/
@[simp]
theorem precomposeSarkisovOfNodalTower_obj_fan (A : LogarithmicProjection i D) :
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
theorem precomposeSarkisovOfNodalTower_obj_hom (A : LogarithmicProjection i D) :
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

-- This proposition allows transport along the structure map and the pole ideal
-- simultaneously, both of which occur in the type of the path's endpoints.
private def hasPathOver {W : Scheme} (f : W ⟶ Z) (s : W ⟶ S)
    (hs : SmoothOfRelativeDimension 2 s) (J : W.IdealSheafData) [IsIntegral W]
    (A B : LogarithmicProjection i D) : Prop :=
  letI : W.Over S := ⟨s⟩
  letI : SmoothOfRelativeDimension 2 (W ↘ S) := hs
  ∃ A' B' : LogarithmicProjection i J,
    A'.fan = A.fan ∧ A'.hom ≍ f ≫ A.hom ∧
    B'.fan = B.fan ∧ B'.hom ≍ f ≫ B.hom ∧ Nonempty (SarkisovPath A' B')

variable {A B : LogarithmicProjection i D}

private theorem hasPathOver_append {m : ℕ} {Y : Scheme} {U : BlowupTower W m Y}
    (hU : IsNodalBoundaryTower Total[D,T] (T.toBase ≫ Z ↘ S) (𝟙 W) U) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    letI : IsNoetherian W := T.isNoetherian
    letI : IsIntegral Y := integral[hU]
    hasPathOver (U.toBase ≫ T.toBase) (U.toBase ≫ W ↘ S) smooth[hU]
      Total[Total[D,T],U] A B →
    ∃ hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U),
      hasPathOver (T.append U).toBase ((T.append U).toBase ≫ Z ↘ S)
        smooth[hTU] Total[D,T.append U] A B := by
  intro h
  have hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U) :=
    hT.append (hU.congr (by simp) (by simp))
  have hbase := toBase_append T U
  have hs : (T.append U).toBase ≫ Z ↘ S = U.toBase ≫ T.toBase ≫ Z ↘ S := by
    rw [hbase, Category.assoc]
  have hJ : Total[D,T.append U] = Total[Total[D,T],U] := by
    rw [hbase, radical_comap_radical, comap_comp]
  refine ⟨hTU, ?_⟩
  have transport {f g : Y ⟶ Z} {s t : Y ⟶ S}
      {hs : SmoothOfRelativeDimension 2 s} {ht : SmoothOfRelativeDimension 2 t}
      {J K : Y.IdealSheafData} [IsIntegral Y]
      (hfg : f = g) (hst : s = t) (hJK : J = K) :
      hasPathOver f s hs J A B ↔ hasPathOver g t ht K A B := by
    subst g t K
    rfl
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let : IsNoetherian W := T.isNoetherian
  let : IsIntegral Y := integral[hU]
  exact (transport hbase hs hJ).mpr h

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
    ∀ {C : LogarithmicProjection i Total[D,T]}
      (_ : SarkisovPath (obj[lift[hT],A]) C)
      {A' B' : LogarithmicProjection i Total[Total[D,T],U]}
      (_ : SarkisovPath A' B'),
      A'.fan = C.fan → A'.hom ≍ U.toBase ≫ C.hom →
      B'.fan = B.fan → B'.hom ≍ U.toBase ≫ T.toBase ≫ B.hom →
      ∃ hTU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) (T.append U),
        letI : Y.Over S := over[T.append U]
        letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hTU]
        letI : IsIntegral Y := integral[hTU]
        ∃ A'' B'' : LogarithmicProjection i Total[D,T.append U],
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
  let F := precomposeSarkisovOfNodalTower (i := i) hRank hE hENode hU
  have hC : obj[F,C] = A' :=
    LogarithmicProjection.ext
      ((precomposeSarkisovOfNodalTower_obj_fan ..).trans hA'.symm)
      ((precomposeSarkisovOfNodalTower_obj_hom ..).trans hAh.symm)
  let A'' := obj[F,obj[lift[hT],A]]
  have hAf : A''.fan = A.fan :=
    (precomposeSarkisovOfNodalTower_obj_fan hRank hE hENode hU _).trans
      (precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT _)
  have hAh' : A''.hom ≍ (U.toBase ≫ T.toBase) ≫ A.hom := by
    have h₁ := precomposeSarkisovOfNodalTower_obj_hom hRank hE hENode hU (obj[lift[hT],A])
    have h₂ := precomposeSarkisovOfNodalTower_obj_hom hRank hD hNode hT A
    have hf := precomposeSarkisovOfNodalTower_obj_fan hRank hD hNode hT A
    exact h₁.trans (by
      rw [Category.assoc]
      exact heq_comp rfl rfl (congrArg Fan.algebraicRealization hf) HEq.rfl h₂)
  exact hasPathOver_append hT hU
    ⟨A'', B', hAf, hAh', hB', by simpa only [Category.assoc] using hBh,
      ⟨@Quiver.Path.comp _ sarkisovQuiver _ _ _ (hC ▸ mapPath[F,p]) q⟩⟩

include hD hNode hRank in
private theorem hasPathOver_of_path (p : SarkisovPath A B) :
    letI : W.Over S := over[T]
    letI : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
    letI : IsIntegral W := integral[hT]
    hasPathOver T.toBase (T.toBase ≫ Z ↘ S) smooth[hT] Total[D,T] A B := by
  let : W.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hT]
  let : IsIntegral W := integral[hT]
  let F := lift[hT]
  let A' : LogarithmicProjection i Total[D,T] := obj[F,A]
  let B' : LogarithmicProjection i Total[D,T] := obj[F,B]
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
      LogarithmicProjection i E → LogarithmicProjection i E → ℕ ×ₗ ℕ → Prop)
    (step : ∀ {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
      [IsIntegral X] [IsNoetherian X] {E : X.IdealSheafData}
      (C F : LogarithmicProjection i E) (bidegree : ℕ ×ₗ ℕ)
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
          let lift := precomposeSarkisovOfNodalTower (i := i) hRank hE hENode hU
          ∃ C' : LogarithmicProjection i Total[E,U],
            Nonempty (SarkisovPath (obj[lift,C]) C') ∧ P C' (obj[lift,F]) next)
    (bidegree : ℕ ×ₗ ℕ) (hP : P A B bidegree) :
    ∃ (k : ℕ) (Y : Scheme) (U : BlowupTower Z k Y)
      (hU : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) U),
      letI : Y.Over S := over[U]
      letI : SmoothOfRelativeDimension 2 (Y ↘ S) := smooth[hU]
      letI : IsIntegral Y := integral[hU]
      ∃ A' B' : LogarithmicProjection i Total[D,U],
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
        exact hBh.trans (heq_comp rfl rfl (congrArg Fan.algebraicRealization hf) HEq.rfl h)
      obtain ⟨hUT, hpath⟩ := exists_comp_sarkisovPath_on_nodalTower hRank hD hNode hU hT p q
        hA' hAh (hB'.trans (precomposeSarkisovOfNodalTower_obj_fan ..)) hBhom
      exact ⟨k + l, W, U.append T, hUT, hpath⟩

end TauCeti.Toric.Fan.LogarithmicProjection
