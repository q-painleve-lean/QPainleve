/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization
public import QPainleve.Geometry.Toric.Fan.Mutation.Resolution
public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic
import QPainleve.Geometry.Toric.Fan.Scheme

/-!
# Resolved Sarkisov links between toric surfaces

A factorization may alternate toric star subdivisions, elementary transformations at
smooth boundary points, and toric isomorphisms. On a common resolving surface, each
vertex of the path gives a regular representative of the corresponding partial
composite with the same pole ideal. Further nodal refinements preserve the links
and their rational maps. Use `open scoped Sarkisov` for the quiver of mixed steps.

The admissible links and the regularity requirement come from Theorem 8.4 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory PointedCone
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "toricMap[" Φ "," Ψ "]" =>
  Scheme.PartialIso.toRationalMap (Fan.denseTorusPartialIso Φ Ψ)
local notation "isoMap[" e "," c "]" =>
  Scheme.Hom.toRationalMap (FanHom.algebraicMap (FanEquiv.toFanHom e) ≫
    Iso.hom (Fan.torusTranslation _ c))

/-- A single allowed link of the toric Sarkisov factorization on a fixed lattice. -/
inductive IsSarkisovLink : {Φ Ψ : Fan i} → (X[Φ] ⤏ X[Ψ]) → Prop
  /-- Blow up a toric fixed point. -/
  | blowup {Φ Ψ : Fan i} [Nonempty Φ.cones] [Nonempty Ψ.cones]
      (h : Φ.IsTwoRayStarSubdivision Ψ) : IsSarkisovLink toricMap[Φ,Ψ]
  /-- Contract the exceptional curve of a toric blowup. -/
  | blowdown {Φ Ψ : Fan i} [Nonempty Φ.cones] [Nonempty Ψ.cones]
      (h : Ψ.IsTwoRayStarSubdivision Φ) : IsSarkisovLink toricMap[Φ,Ψ]
  /-- An elementary transformation at a nonzero binomial center on a pivot ray. -/
  | mutation {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N) (ρ : Φ.Ray) (c : ℂˣ)
      (hneg : hull ℝ {i (-ρ.primitiveGenerator)} ∈ Φ.cones) :
      IsSarkisovLink (Φ.mutationPartialMap b (c : ℂ) ρ.primitiveGenerator_ne_zero
        ρ.hull_primitiveGenerator_mem hneg).toRationalMap
  /-- A fan equivalence followed by a torus translation. -/
  | toricIso {Φ Ψ : Fan i} [Nonempty Ψ.cones]
      (e : FanEquiv Φ Ψ) (c : Multiplicative (N →+ ℤ) →* ℂˣ) :
      IsSarkisovLink isoMap[e,c]

/-- Every allowed link has dense image. -/
theorem IsSarkisovLink.isDominant {Φ Ψ : Fan i} {f : X[Φ] ⤏ X[Ψ]}
    (hf : IsSarkisovLink f) : f.IsDominant := by
  cases hf <;> infer_instance

namespace LogarithmicProjection

variable {Z : Scheme} [Z.Over S] [SmoothOfRelativeDimension 2 (Z ↘ S)]
  [PreirreducibleSpace Z]
  {D : Z.IdealSheafData} {A B C : LogarithmicProjection i D}

/-- An allowed link whose composite with the specified source projection has the
specified target projection as a regular representative. -/
@[ext]
structure SarkisovStep (A B : LogarithmicProjection i D) where
  /-- The rational map between the toric targets. -/
  rationalMap : X[A.fan] ⤏ X[B.fan]
  /-- The rational map is an allowed link. -/
  isSarkisovLink : IsSarkisovLink rationalMap
  /-- The link is resolved by the two given projections. -/
  comp_rationalMap : A.hom.toRationalMap.comp rationalMap = B.hom.toRationalMap

instance (e : SarkisovStep A B) : e.rationalMap.IsDominant :=
  e.isSarkisovLink.isDominant

/-- The quiver of resolved Sarkisov steps. -/
abbrev sarkisovQuiver : Quiver (LogarithmicProjection i D) where
  Hom := SarkisovStep

/-- A finite path of resolved Sarkisov steps. -/
abbrev SarkisovPath (A B : LogarithmicProjection i D) := @Quiver.Path _ sarkisovQuiver A B

/-- Regard a resolved toric star step as a Sarkisov step. -/
def StarStep.toSarkisovStep (e : StarStep A B) :
    SarkisovStep A B where
  rationalMap := toricMap[A.fan,B.fan]
  isSarkisovLink := by
    cases e with
    | blowup h _ => exact .blowup h
    | blowdown h _ => exact .blowdown h
  comp_rationalMap := e.comp_toRationalMap

scoped[Sarkisov] attribute [instance] TauCeti.Toric.Fan.LogarithmicProjection.sarkisovQuiver

open scoped Sarkisov

namespace SarkisovPath

/-- Regard a resolved toric star path as a path of Sarkisov steps. -/
def ofStar (p : @Quiver.Path _ instQuiver A B) : SarkisovPath A B :=
  let F := @Prefunctor.mk (LogarithmicProjection i D) instQuiver
    (LogarithmicProjection i D) sarkisovQuiver id (fun e ↦ StarStep.toSarkisovStep e)
  @Prefunctor.mapPath _ instQuiver _ sarkisovQuiver F _ _ p

/-- The composite of the links along a resolved path, in execution order. -/
def rationalMap (p : SarkisovPath A B) : X[A.fan] ⤏ X[B.fan] :=
  (dominantPathRationalMap sarkisovQuiver (fun e ↦ ⟨e.rationalMap, inferInstance⟩) p).val

instance (p : SarkisovPath A B) : p.rationalMap.IsDominant :=
  (dominantPathRationalMap sarkisovQuiver (fun e ↦ ⟨e.rationalMap, inferInstance⟩) p).property

@[simp]
theorem rationalMap_nil :
    rationalMap (.nil : SarkisovPath A A) = Scheme.RationalMap.id _ := (rfl)

@[simp]
theorem rationalMap_cons (p : SarkisovPath A B) (e : SarkisovStep B C) :
    rationalMap (p.cons e) = p.rationalMap.comp e.rationalMap := (rfl)

/-- The endpoint projection is the regular representative of the composite
on the resolving surface. This applies to every initial subpath. -/
theorem comp_rationalMap (p : SarkisovPath A B) :
    A.hom.toRationalMap.comp p.rationalMap = B.hom.toRationalMap := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simpa only [rationalMap_cons, ← Scheme.RationalMap.comp_assoc, ih] using
      SarkisovStep.comp_rationalMap e

/-- The path realizes a prescribed rational map exactly when its endpoint projections
give a regular representative of that map on the resolving surface. -/
theorem rationalMap_eq_iff [IsIntegral Z] (p : SarkisovPath A B) (f : X[A.fan] ⤏ X[B.fan]) :
    p.rationalMap = f ↔ A.hom.toRationalMap.comp f = B.hom.toRationalMap :=
  ⟨fun h ↦ h ▸ p.comp_rationalMap,
    fun h ↦ A.hom.toRationalMap.comp_left_injective (p.comp_rationalMap.trans h.symm)⟩

@[simp]
theorem rationalMap_comp (p : SarkisovPath A B) (q : SarkisovPath B C) :
    rationalMap (p.comp q) = p.rationalMap.comp q.rationalMap := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, rationalMap_cons, ih, Scheme.RationalMap.comp_assoc]

/-- Toric star paths give the same rational map when included as Sarkisov paths. -/
@[simp]
theorem rationalMap_ofStar [IsIntegral Z] (p : @Quiver.Path _ instQuiver A B) :
    rationalMap (ofStar p) = pathRationalMap p :=
  (rationalMap_eq_iff _ _).mpr (comp_pathRationalMap p)

end SarkisovPath

section Refinement

variable {W : Scheme} [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)]
  [PreirreducibleSpace W] {E : W.IdealSheafData}
  (hN : Module.finrank ℤ N = 2) (f : W ⟶ Z) [f.IsOver S] [IsDominant f]
  (hf : letI : Smooth (W ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    D.comap f = E * ramificationIdealSheaf ℂ f)

/-- Precompose the regular representatives of a Sarkisov factorization with a
dominant morphism carrying the pole ideal. The toric targets and links are preserved. -/
def precomposeSarkisov :
    @Prefunctor (LogarithmicProjection i D) sarkisovQuiver
      (LogarithmicProjection i E) sarkisovQuiver where
  obj := precomposeProjection hN f hf
  map {A B} e :=
    { rationalMap := e.rationalMap
      isSarkisovLink := e.isSarkisovLink
      comp_rationalMap := by
        let : IrreducibleSpace Z :=
          { isPreirreducible_univ := PreirreducibleSpace.isPreirreducible_univ
            toNonempty := A.hom.denseRange.nonempty }
        -- The objects of `precompose` keep the original fans and compose the projections.
        change (f ≫ A.hom).toRationalMap.comp e.rationalMap = (f ≫ B.hom).toRationalMap
        have hc := congrArg (fun m ↦ f.toRationalMap.comp m) e.comp_rationalMap
        rw [← Scheme.RationalMap.comp_assoc f.toRationalMap A.hom.toRationalMap e.rationalMap] at hc
        simpa only [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
          using hc }

@[simp]
theorem precomposeSarkisov_obj_fan (A : LogarithmicProjection i D) :
    ((precomposeSarkisov hN f hf).obj A).fan = A.fan := (rfl)

/-- The projection to a toric target after refining the resolving surface. -/
theorem precomposeSarkisov_obj_hom (A : LogarithmicProjection i D) :
    ((precomposeSarkisov hN f hf).obj A).hom ≍ f ≫ A.hom :=
  (HEq.rfl)

/-- Precomposition leaves the rational map between the toric targets of each link fixed. -/
theorem precomposeSarkisov_map_rationalMap (e : SarkisovStep A B) :
    ((precomposeSarkisov hN f hf).map e).rationalMap ≍ e.rationalMap :=
  (HEq.rfl)

/-- Refining the resolving surface preserves the rational map of a Sarkisov path. -/
theorem SarkisovPath.rationalMap_mapPath_precompose (p : SarkisovPath A B) :
    rationalMap ((precomposeSarkisov hN f hf).mapPath p) ≍ p.rationalMap := by
  induction p with
  | nil => exact HEq.rfl
  | cons p e ih =>
    -- Precomposition leaves the fans and the rational map on each edge unchanged.
    change (rationalMap ((precomposeSarkisov hN f hf).mapPath p)).comp e.rationalMap ≍
      (rationalMap p).comp e.rationalMap
    simp only [eq_of_heq ih]
    rfl

end Refinement

open QPainleve.BlowupTower in
/-- Lift an entire Sarkisov path through a nodal extension of its resolving surface.
If the last projection on that extension is already specified, it serves as the endpoint
of the lifted path. Thus a subsequent block starting at that actual projection can be
appended with `Quiver.Path.comp`. The pole divisor on the extension is the reduced total
transform and the rational map between toric targets is preserved. -/
theorem SarkisovPath.exists_precompose_of_nodalTower [IsIntegral Z] [IsNoetherian Z]
    (p : SarkisovPath A B) {n : ℕ} {Y W : Scheme} {T : QPainleve.BlowupTower Z n Y}
    [W.Over S] [SmoothOfRelativeDimension 2 (W ↘ S)] [PreirreducibleSpace W]
    (hRank : Module.finrank ℤ N = 2) (hT : IsNodalBoundaryTower D (Z ↘ S) (𝟙 Z) T)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ Z ↘ S))
    (e : W ≅ Y) (q : W ⟶ Z) [q.IsOver S] (hq : e.hom ≫ T.toBase = q)
    (C : LogarithmicProjection i (D.comap q).radical)
    (hFan : C.fan = B.fan) (hHom : C.hom ≍ q ≫ B.hom) :
    ∃ (F : @Prefunctor (LogarithmicProjection i D) sarkisovQuiver
        (LogarithmicProjection i (D.comap q).radical) sarkisovQuiver)
      (hEnd : F.obj B = C),
      (∀ L, (F.obj L).fan = L.fan ∧ (F.obj L).hom ≍ q ≫ L.hom) ∧
      (∀ {L M} (a : SarkisovStep L M), (F.map a).rationalMap ≍ a.rationalMap) ∧
      ((hEnd ▸ F.mapPath p : SarkisovPath (F.obj A) C)).rationalMap ≍ p.rationalMap := by
  let : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Z ↘ S)
  let : IsDominant q := hq ▸ inferInstanceAs (IsDominant (e.hom ≫ T.toBase))
  have hPole := hT.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hNode e q hq
  let F := precomposeSarkisov (i := i) hRank q hPole
  have hEnd : F.obj B = C := by
    exact LogarithmicProjection.ext ((precomposeSarkisov_obj_fan ..).trans hFan.symm)
      ((precomposeSarkisov_obj_hom ..).trans hHom.symm)
  refine ⟨F, hEnd, fun L ↦ ⟨precomposeSarkisov_obj_fan .., precomposeSarkisov_obj_hom ..⟩,
    fun a ↦ precomposeSarkisov_map_rationalMap hRank q hPole a, ?_⟩
  subst C
  exact p.rationalMap_mapPath_precompose hRank q hPole

end LogarithmicProjection

end TauCeti.Toric.Fan
