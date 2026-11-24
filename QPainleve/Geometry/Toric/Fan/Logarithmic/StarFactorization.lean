/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Combinatorics.Quiver.Symmetric
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
public import QPainleve.Geometry.Toric.Fan.Birational
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Resolved factorizations of toric changes

A regular common refinement gives a path of toric blowups and blowdowns between
two complete regular fans. With a dominant map to the refinement, every vertex of
the path carries the actual composite from the resolving surface. The logarithmic
pole ideal is the same at every vertex.

This is the toric change of model used in the proof of Theorem 8.4 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)

/-- A specified dominant projection from a smooth surface to a complete regular
toric variety, with the pole factorization of its pulled-back toric boundary. -/
@[ext]
structure LogarithmicProjection (i : N →+ V) {Z : Scheme} [Z.Over S]
    [SmoothOfRelativeDimension 2 (Z ↘ S)] (D : Z.IdealSheafData) where
  /-- The target fan. -/
  fan : Fan i
  /-- The target fan is regular. -/
  isRegular : fan.IsRegular
  /-- The target fan is complete. -/
  isComplete : fan.IsComplete
  /-- The specified regular map on the resolving surface. -/
  hom : Z ⟶ X[fan]
  /-- The projection is over the complex numbers. -/
  isOver : hom.IsOver S
  /-- The projection is dominant. -/
  isDominant : IsDominant hom
  /-- The pulled-back toric boundary is the pole ideal times the ramification ideal. -/
  comap_boundaryIdeal : letI : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (fan.boundaryIdeal isComplete.nonempty_cones).comap hom =
      D * ramificationIdealSheaf ℂ hom

namespace LogarithmicProjection

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  {D : Z.IdealSheafData} {A B C : LogarithmicProjection i D}

instance (A : LogarithmicProjection i D) : Nonempty A.fan.cones :=
  A.isComplete.nonempty_cones

attribute [instance] LogarithmicProjection.isDominant LogarithmicProjection.isOver

/-- A step of a resolved toric factorization. The maps from the resolving surface
form the commutative triangle with the star subdivision projection. -/
inductive StarStep : LogarithmicProjection i D → LogarithmicProjection i D → Type
  /-- Pass to the star subdivision at a two-ray cone. -/
  | blowup {A B : LogarithmicProjection i D} (h : A.fan.IsTwoRayStarSubdivision B.fan)
      (comm : B.hom ≫ π[h.isSubdivision] = A.hom) : StarStep A B
  /-- Contract from a star subdivision at a two-ray cone. -/
  | blowdown {A B : LogarithmicProjection i D} (h : B.fan.IsTwoRayStarSubdivision A.fan)
      (comm : A.hom ≫ π[h.isSubdivision] = B.hom) : StarStep A B

instance : Quiver (LogarithmicProjection i D) where
  Hom := StarStep

instance : Quiver.HasInvolutiveReverse (LogarithmicProjection i D) where
  reverse'
    | .blowup h comm => .blowdown h comm
    | .blowdown h comm => .blowup h comm
  inv' e := by cases e <;> rfl

/-- A resolved toric star step carries the modification property from its source
projection to its target projection. -/
theorem StarStep.isModification_target (step : StarStep A B)
    (hN : Module.finrank ℤ N = 2) (hA : IsModification A.hom) : IsModification B.hom := by
  cases step with
  | blowup h comm =>
    let H := h.isSubdivision
    let : IsModification π[H] :=
      H.isModification_algebraicMap A.isRegular B.isRegular A.isComplete.nonempty_cones hN
    let : IsModification (B.hom ≫ π[H]) := comm.symm ▸ hA
    exact IsModification.of_comp_right B.hom π[H]
  | blowdown h comm =>
    let H := h.isSubdivision
    let : IsModification A.hom := hA
    let : IsModification π[H] :=
      H.isModification_algebraicMap B.isRegular A.isRegular B.isComplete.nonempty_cones hN
    rw [← comm]
    infer_instance

local notation "toricMap[" A "," B "]" =>
  Scheme.PartialIso.toRationalMap
    (Fan.denseTorusPartialIso (LogarithmicProjection.fan A) (LogarithmicProjection.fan B))

/-- Each toric step composed with the source projection is the specified target projection
as a rational map on the resolving surface. -/
theorem StarStep.comp_toRationalMap [PreirreducibleSpace Z] (e : StarStep A B) :
    A.hom.toRationalMap.comp toricMap[A,B] = B.hom.toRationalMap := by
  cases e with
  | blowup h comm =>
    have hs := h.isSubdivision.comp_denseTorusPartialIso (.refl B.fan) B.hom
    simpa only [IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, Category.comp_id, comm]
      using hs
  | blowdown h comm =>
    rw [← h.isSubdivision.toRationalMap_algebraicMap, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom, comm]

private def dominantPathRationalMap {A : LogarithmicProjection i D} :
    ∀ {B : LogarithmicProjection i D}, Quiver.Path A B →
      {f : X[A.fan] ⤏ X[B.fan] // f.IsDominant}
  | _, .nil => ⟨Scheme.RationalMap.id _, inferInstance⟩
  | B, @Quiver.Path.cons _ _ _ C _ p _ =>
    let f := dominantPathRationalMap p
    haveI := f.property
    ⟨f.val.comp toricMap[C,B], inferInstance⟩

/-- Compose the rational maps of a resolved toric path in execution order. -/
def pathRationalMap (p : Quiver.Path A B) : X[A.fan] ⤏ X[B.fan] :=
  (dominantPathRationalMap p).val

instance (p : Quiver.Path A B) : (pathRationalMap p).IsDominant :=
  (dominantPathRationalMap p).property

@[simp]
theorem pathRationalMap_nil :
    pathRationalMap (Quiver.Path.nil : Quiver.Path A A) = Scheme.RationalMap.id _ := (rfl)

@[simp]
theorem pathRationalMap_cons (p : Quiver.Path A B) (e : B ⟶ C) :
    pathRationalMap (p.cons e) = (pathRationalMap p).comp toricMap[B,C] := (rfl)

/-- A path of toric steps induces the rational map given by the common dense torus. -/
theorem pathRationalMap_eq_denseTorusPartialIso (p : Quiver.Path A B) :
    pathRationalMap p = toricMap[A,B] := by
  induction p with
  | nil => rw [pathRationalMap_nil, denseTorusPartialIso_self_toRationalMap]
  | cons p e ih => simp only [pathRationalMap_cons, ih, denseTorusPartialIso_toRationalMap_comp]

/-- The regular projections at the vertices of a path represent its partial composites.
Apply this to any initial subpath, including the whole path. -/
theorem comp_pathRationalMap [PreirreducibleSpace Z] (p : Quiver.Path A B) :
    A.hom.toRationalMap.comp (pathRationalMap p) = B.hom.toRationalMap := by
  induction p with
  | nil => simp only [pathRationalMap_nil, Scheme.RationalMap.comp_id]
  | cons p e ih =>
    simpa only [pathRationalMap_cons, ← Scheme.RationalMap.comp_assoc, ih] using
      StarStep.comp_toRationalMap e

/-- Concatenation of resolved paths composes their rational maps in execution order. -/
theorem pathRationalMap_comp (p : Quiver.Path A B) (q : Quiver.Path B C) :
    pathRationalMap (p.comp q) = (pathRationalMap p).comp (pathRationalMap q) := by
  simp only [pathRationalMap_eq_denseTorusPartialIso, denseTorusPartialIso_toRationalMap_comp]

section Factorization

/-- The projection to a regular coarsening, with the logarithmic pole ideal carried
through the subdivision morphism. -/
def coarsen (C : LogarithmicProjection i D) {Φ : Fan i}
    (H : C.fan.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) :
    LogarithmicProjection i D := by
  have hc := H.isComplete_iff.mp C.isComplete
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 (X[C.fan] ↘ S) := by
    rw [C.fan.algebraicRealization_over, ← hN]
    exact C.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap C.isRegular
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    rw [Φ.algebraicRealization_over, ← hN]
    exact Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact
    { fan := Φ
      isRegular := hΦ
      isComplete := hc
      hom := C.hom ≫ π[H]
      isOver := inferInstance
      isDominant := inferInstance
      comap_boundaryIdeal := comap_eq_mul_ramificationIdealSheaf_comp ℂ C.hom π[H] 2
        (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hΦ C.isRegular hc hN)
        C.comap_boundaryIdeal }

@[simp]
theorem coarsen_fan (C : LogarithmicProjection i D) {Φ : Fan i}
    (H : C.fan.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) :
    (C.coarsen H hΦ hN).fan = Φ := (rfl)

/-- The coarsened projection is the composite with the subdivision morphism. -/
theorem coarsen_hom (C : LogarithmicProjection i D) {Φ : Fan i}
    (H : C.fan.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hN : Module.finrank ℤ N = 2) :
    (C.coarsen H hΦ hN).hom ≍ C.hom ≫ π[H] := (HEq.rfl)

private theorem nonempty_blowupPath (C : LogarithmicProjection i D)
    (hN : Module.finrank ℤ N = 2) {Φ Ψ : Fan i} (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (h : Relation.ReflTransGen IsTwoRayStarSubdivision Φ Ψ) (K : C.fan.IsSubdivision Ψ) :
    Nonempty (Quiver.Path (C.coarsen (K.trans (isSubdivision_of_starSubdivision_chain h)) hΦ hN)
      (C.coarsen K hΨ hN)) := by
  induction h with
  | refl => exact ⟨.nil⟩
  | @tail Δ Ψ hchain hstep ih =>
    have hΔ : Δ.IsRegular := by cases hstep with | along hΔ => exact hΔ
    obtain ⟨p⟩ := ih hΔ (K.trans hstep.isSubdivision)
    refine ⟨p.cons (.blowup hstep ?_)⟩
    -- The endpoint fans are definitionally Ψ and Δ, so this is subdivision composition.
    change (C.hom ≫ π[K]) ≫ π[hstep.isSubdivision] = C.hom ≫ π[K.trans hstep.isSubdivision]
    rw [IsSubdivision.toFanHom_trans K hstep.isSubdivision, FanHom.algebraicMap_comp,
      Category.assoc]

/-- A subdivision between regular fans lifts to a path of resolved toric steps.
The same projection to the fine fan determines all intermediate projections. -/
theorem nonempty_path_of_subdivision (C : LogarithmicProjection i D)
    (hN : Module.finrank ℤ N = 2) {Φ : Fan i} (hΦ : Φ.IsRegular)
    (H : C.fan.IsSubdivision Φ) :
    Nonempty (Quiver.Path (C.coarsen H hΦ hN) C) := by
  have h := H.exists_starSubdivision_factorization hΦ C.isRegular hN
  have hpath := nonempty_blowupPath C hN hΦ C.isRegular h (.refl C.fan)
  have hself : C.coarsen (.refl C.fan) C.isRegular hN = C := by
    refine LogarithmicProjection.ext (coarsen_fan ..) ((coarsen_hom ..).trans ?_)
    exact heq_of_eq (by simp only [IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id,
      Category.comp_id])
  rwa [hself] at hpath

/-- Factor the dense-torus change between two regular coarsenings into blowups and
blowdowns on a single specified resolving surface. The endpoints are the given maps,
and every intermediate projection has their common pole ideal. -/
theorem exists_resolved_toric_star_factorization [IsIntegral Z] (A B : LogarithmicProjection i D)
    (hN : Module.finrank ℤ N = 2) {Ω : Fan i} (hΩ : Ω.IsRegular)
    (J : Ω.IsSubdivision A.fan) (K : Ω.IsSubdivision B.fan)
    (g : Z ⟶ X[Ω]) [IsDominant g]
    (hA : g ≫ π[J] = A.hom) (hB : g ≫ π[K] = B.hom) :
    ∃ p : Quiver.Path A B, pathRationalMap p = toricMap[A,B] ∧
      A.hom.toRationalMap.comp (pathRationalMap p) = B.hom.toRationalMap := by
  let hcΩ := J.isComplete_iff.mpr A.isComplete
  let : Nonempty Ω.cones := hcΩ.nonempty_cones
  have hg : g.IsOver S := ⟨by
    rw [Ω.algebraicRealization_over,
      ← J.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap, ← Category.assoc, hA,
      ← A.fan.algebraicRealization_over, comp_over]⟩
  let : g.IsOver S := hg
  have hp := (comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_iff_of_common_subdivision
    J (.refl Ω) A.isRegular hΩ hΩ A.isComplete hN g D).mp (by
      simpa only [hA] using A.comap_boundaryIdeal)
  let C : LogarithmicProjection i D :=
    { fan := Ω
      isRegular := hΩ
      isComplete := hcΩ
      hom := g
      isOver := hg
      isDominant := inferInstance
      comap_boundaryIdeal := by
        simpa only [IsSubdivision.toFanHom_refl, FanHom.algebraicMap_id, Category.comp_id]
          using hp }
  have hcoarseA : C.coarsen J A.isRegular hN = A := by
    exact LogarithmicProjection.ext (coarsen_fan ..) ((coarsen_hom ..).trans (heq_of_eq hA))
  have hcoarseB : C.coarsen K B.isRegular hN = B := by
    exact LogarithmicProjection.ext (coarsen_fan ..) ((coarsen_hom ..).trans (heq_of_eq hB))
  have hpathA := C.nonempty_path_of_subdivision hN A.isRegular J
  have hpathB := C.nonempty_path_of_subdivision hN B.isRegular K
  rw [hcoarseA] at hpathA
  rw [hcoarseB] at hpathB
  obtain ⟨p⟩ := hpathA
  obtain ⟨q⟩ := hpathB
  exact ⟨p.comp q.reverse, pathRationalMap_eq_denseTorusPartialIso _, comp_pathRationalMap _⟩

end Factorization

section Refinement

variable {W : Scheme} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)]
  {E : W.IdealSheafData} (hN : Module.finrank ℤ N = 2) (f : W ⟶ Z) [f.IsOver S] [IsDominant f]
  (hf : letI : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    D.comap f = E * ramificationIdealSheaf ℂ f)

/-- Precompose every projection and commutative triangle by a dominant morphism that
carries the pole factorization. The resulting prefunctor lifts whole paths to the new
resolving surface using `Prefunctor.mapPath`. -/
def precompose : LogarithmicProjection i D ⥤q LogarithmicProjection i E := by
  let refined (A : LogarithmicProjection i D) : LogarithmicProjection i E := by
    let : SmoothOfRelativeDimension 2 (X[A.fan] ↘ S) := by
      rw [A.fan.algebraicRealization_over, ← hN]
      exact A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    exact
      { fan := A.fan
        isRegular := A.isRegular
        isComplete := A.isComplete
        hom := f ≫ A.hom
        isOver := inferInstance
        isDominant := inferInstance
        comap_boundaryIdeal :=
          comap_eq_mul_ramificationIdealSheaf_comp ℂ f A.hom 2 A.comap_boundaryIdeal hf }
  refine ⟨refined, ?_⟩
  intro A B e
  cases e with
  | blowup h comm => exact .blowup h ((Category.assoc _ _ _).trans (congrArg (f ≫ ·) comm))
  | blowdown h comm => exact .blowdown h ((Category.assoc _ _ _).trans (congrArg (f ≫ ·) comm))

@[simp]
theorem precompose_obj_fan (A : LogarithmicProjection i D) :
    ((precompose (i := i) hN f hf).obj A).fan = A.fan := (rfl)

/-- The new projection is the given projection precomposed with the refinement map. -/
theorem precompose_obj_hom (A : LogarithmicProjection i D) :
    ((precompose (i := i) hN f hf).obj A).hom ≍ f ≫ A.hom := (HEq.rfl)

/-- Refining the resolving surface preserves the evaluated rational map of the path. -/
theorem pathRationalMap_mapPath_precompose (p : Quiver.Path A B) :
    pathRationalMap ((precompose hN f hf).mapPath p) ≍ pathRationalMap p := by
  rw [pathRationalMap_eq_denseTorusPartialIso, pathRationalMap_eq_denseTorusPartialIso]
  exact HEq.rfl

end Refinement

open QPainleve.BlowupTower in
/-- A nodal blowup tower lifts any resolved toric path to the reduced total pole boundary.
The projections are obtained by precomposing with the tower, and the lifted path gives
the same rational map between its toric targets. -/
theorem exists_prefunctor_of_nodalTower [IsIntegral Z] [IsNoetherian Z] {n : ℕ} {W : Scheme}
    {T : QPainleve.BlowupTower Z n W}
    (hRank : Module.finrank ℤ N = 2) (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S)) :
    letI : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
    letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
    ∃ F : LogarithmicProjection i D ⥤q LogarithmicProjection i (D.comap T.toBase).radical,
      (∀ A, (F.obj A).fan = A.fan ∧ (F.obj A).hom ≍ T.toBase ≫ A.hom) ∧
      ∀ {A B} (p : Quiver.Path A B), pathRationalMap (F.mapPath p) ≍ pathRationalMap p := by
  let : W.Over S := ⟨T.toBase ≫ Z ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (Z ↘ S)
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  have hPole := hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode (Iso.refl W)
    T.toBase (Category.id_comp _)
  refine ⟨precompose hRank T.toBase hPole, fun A ↦ ⟨precompose_obj_fan .., ?_⟩, ?_⟩
  · exact precompose_obj_hom ..
  · intro A B p
    exact pathRationalMap_mapPath_precompose hRank T.toBase hPole p

end LogarithmicProjection

end TauCeti.Toric.Fan
