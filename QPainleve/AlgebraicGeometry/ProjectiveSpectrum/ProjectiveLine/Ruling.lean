/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import QPainleve.AlgebraicGeometry.Cohomology.Pushforward
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import QPainleve.AlgebraicGeometry.Cohomology.Fiber
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# The rank-two bundle of a projective-line ruling

On a flat ruling with closed fibers isomorphic to the projective line, the direct image of
a line bundle of fiber degree one gives the rank-two bundle for the relative projective
bundle construction. The dimensions on the closed fibers come from the twisting sheaf
`𝒪(1)` and their residue fields agree with the algebraically closed base field.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [hX : X.Over (Spec (.of k))] [hY : Y.Over (Spec (.of k))]
  (f : X ⟶ Y) [hf : f.IsOver (Spec (.of k))] [hft : LocallyOfFiniteType (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)

include hX hY hf hft in
private theorem cohomology_of_degree_one_on_fiber (L : InvertibleSheaf X)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (e : projectiveLine k ≅ f.fiber y)
    (he : e.hom ≫ f.fiberι y ≫ X ↘ S = projectiveLine k ↘ S)
    (hdeg : LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y)
      (LineBundleClass.mk L) = 1) :
    Subsingleton (Cohomology ((Scheme.Modules.pullback (f.fiberι y)).obj L.obj) 1) ∧
      fiberCohomologyFinrank L.obj f 0 y = 2 := by
  let C := f.fiber y
  let : C.Over S := ⟨f.fiberι y ≫ X ↘ S⟩
  let : e.hom.IsOver S := ⟨he⟩
  let M := (Scheme.Modules.pullback (f.fiberι y)).obj L.obj
  let L' := (InvertibleSheaf.pullback (e.hom ≫ f.fiberι y)).obj L
  have hd : InvertibleSheaf.eulerDegree k L' = 1 := by
    simpa only [L', LineBundleClass.intersectionNumber_def, LineBundleClass.pullback_mk,
      LineBundleClass.eulerDegree_mk] using hdeg
  obtain ⟨t⟩ := (projectiveLine.nonempty_iso_twistingSheaf_iff k L' 1).mpr hd
  let a : (Scheme.Modules.pullback e.hom).obj M ≅ Proj.twistingSheaf 𝒜 1 :=
    ((pullbackComp e.hom (f.fiberι y)).app L.obj) ≪≫
      eqToIso (InvertibleSheaf.pullback_obj_obj _ _).symm ≪≫ t
  let b (i : ℕ) := (e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k M i).symm.trans
    (cohomologyBaseLinearEquivOfIso k a i)
  have hzero : Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 1) 1) :=
    (Pi.basisFun k (Fin 2)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt
      (by decide) Nat.one_pos
  refine ⟨(b 1).injective.subsingleton, ?_⟩
  rw [f.fiberCohomologyFinrank_eq_finrank_of_isClosed (k := k) hy, (b 0).finrank_eq,
    projectiveLine.finrank_cohomology_zero_twistingSheaf]
  decide

variable [hsep : IsSeparated (Y ↘ Spec (.of k))] [hproj : X.IsProjectiveOver k] [Flat f]

include hX hY hf hft hsep hproj in
/-- The direct image of a line bundle of degree one on the closed projective-line fibers
is a vector bundle of rank two. The fiber isomorphisms are over the base field. -/
theorem exists_rankTwo_pushforward_of_projectiveLine_fibers (L : InvertibleSheaf X)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → ∃ e : projectiveLine k ≅ f.fiber y,
      e.hom ≫ f.fiberι y ≫ X ↘ S = projectiveLine k ↘ S ∧
        LineBundleClass.intersectionNumber k (e.hom ≫ f.fiberι y) (LineBundleClass.mk L) = 1) :
    ∃ V : FiniteLocallyFreeSheaf.FixedRank Y 2, V.obj.obj = (pushforward f).obj L.obj := by
  let E := (InvertibleSheaf.toFiniteLocallyFree X).obj L
  have hE : E.obj = L.obj := rfl
  refine (f.exists_fixedRank_pushforward (k := k) E 2 ?_ ?_ ?_).imp fun V hV ↦
    hV.trans (congrArg (pushforward f).obj hE)
  · intro y hy
    obtain ⟨e, -, -⟩ := h y hy
    rw [← e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq,
      Scheme.IsCurveOver.topologicalKrullDim_eq_one k]
  · intro y hy
    obtain ⟨e, he, hdeg⟩ := h y hy
    rw [hE]
    exact (f.cohomology_of_degree_one_on_fiber L hy e he hdeg).1
  · intro y hy
    obtain ⟨e, he, hdeg⟩ := h y hy
    rw [hE]
    exact (f.cohomology_of_degree_one_on_fiber L hy e he hdeg).2

end AlgebraicGeometry.Scheme.Hom
