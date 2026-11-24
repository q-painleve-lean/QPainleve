/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import QPainleve.AlgebraicGeometry.RelativeProj.Fiber
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper

import QPainleve.AlgebraicGeometry.LineBundle.Fiber
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Degree
import QPainleve.AlgebraicGeometry.RelativeProj.Smooth
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.Fibers.Composition
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Degree-one comparisons with a projective bundle

A proper family of integral curves over a quasi-compact reduced Jacobson base
is identified with a rank-two projective bundle by a comparison map whose
tautological pullback has degree one on the closed fibers. The comparison uses
`Scheme.Hom.isIso_of_eulerDegree_pullback_closed_fibers_eq_one` and the
identification of the polarized fibers of a rank-two projective bundle.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

variable {X S : Scheme.{u}} (E : FiniteLocallyFreeSheaf.FixedRank S 2)

local notation "F" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent S) (ObjectProperty.FullSubcategory.obj E)
local notation "A" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra S) F)
local notation "p" => CommMon.relativeProjToBase A
local notation "P" => CommMon.relativeProj A
local notation "𝒪₁" =>
  LineBundleClass.mk (ObjectProperty.FullSubcategory.mk (CommMon.relativeProjTwistingSheaf A 1)
    inferInstance : InvertibleSheaf P)

/-- A comparison from a proper family of integral curves to a rank-two projective
bundle over a quasi-compact reduced Jacobson scheme is an isomorphism if the
pullback of the tautological line bundle has degree one on every closed fiber. -/
theorem isIso_of_degree_one_to_relativeProj [CompactSpace S] [IsReduced S] [JacobsonSpace S]
    (f : X ⟶ P) {g : X ⟶ S} [IsProper g] (hf : f ≫ p = g)
    (hX : ∀ s : S, IsClosed ({s} : Set S) →
      let := g.fiberOverSpecResidueField s
      (g.fiber s).IsCurveOver (S.residueField s))
    (hL : ∀ s : S, IsClosed ({s} : Set S) →
      let := g.fiberOverSpecResidueField s
      eulerDegree (S.residueField s)
        (LineBundleClass.pullback (g.fiberι s) (LineBundleClass.pullback f 𝒪₁)) = 1) :
    IsIso f := by
  subst g
  have : SmoothOfRelativeDimension 1 p := E.smoothOfRelativeDimension_relativeProjToBase
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : IsReduced P := Scheme.Hom.isReduced_of_smooth p
  have : (ObjectProperty.FullSubcategory.obj F).IsFiniteType := by
    rw [FiniteLocallyFreeSheaf.toQuasicoherent_obj_obj]
    infer_instance
  have : IsProper f := IsProper.of_comp f p
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace p
  exact f.isIso_of_eulerDegree_pullback_closed_fibers_eq_one p
    (Scheme.Hom.closedPoints_subset_preimage_closedPoints p) 𝒪₁
    (fun s _ ↦ E.exists_relativeProj_fiber_iso_projectiveLine s) hX hL

/-- A proper ruling over an algebraically closed field is identified with the given
rank-two projective bundle by a comparison over a quasi-compact reduced base that pulls back the
tautological line bundle to the given class of closed-fiber degree one. The fiber
isomorphisms and degrees can be given over the ground field. -/
theorem isIso_of_projectiveLine_fibers_of_pullback_twistingSheaf {k : Type u}
    [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [CompactSpace S] [IsReduced S]
    (f : X ⟶ P) {g : X ⟶ S} [IsProper g] [g.IsOver (Spec (.of k))] (hf : f ≫ p = g)
    (L : LineBundleClass X) (hL : LineBundleClass.pullback f 𝒪₁ = L)
    (h : ∀ s : S, IsClosed ({s} : Set S) → ∃ e : projectiveLine k ≅ g.fiber s,
      e.hom ≫ g.fiberι s ≫ X ↘ Spec (.of k) = projectiveLine k ↘ Spec (.of k) ∧
        intersectionNumber k (e.hom ≫ g.fiberι s) L = 1) :
    IsIso f := by
  let : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace (S ↘ Spec (.of k))
  refine E.isIso_of_degree_one_to_relativeProj f hf ?_ ?_
  · intro s hs
    obtain ⟨e, _, _⟩ := h s hs
    let := g.fiberOverSpecResidueField s
    -- The curve predicate uses the scheme-theoretic fiber's residue-field structure map.
    change (g.fiber s).IsCurveOver (S.residueField s)
    let : IsIntegral (g.fiber s) := IsIntegral.of_isIso e.hom
    let : IsProper (g.fiber s ↘ Spec (S.residueField s)) :=
      g.isProper_fiberToSpecResidueField s
    exact Scheme.IsCurveOver.mk (by
      rw [← e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq,
        Scheme.IsCurveOver.topologicalKrullDim_eq_one k])
  · intro s hs
    obtain ⟨e, he, hd⟩ := h s hs
    let : (g.fiber s).Over (Spec (.of k)) := ⟨g.fiberι s ≫ X ↘ Spec (.of k)⟩
    let := g.fiberOverSpecResidueField s
    have hdeg : eulerDegree k (LineBundleClass.pullback (g.fiberι s) L) = 1 := by
      rw [intersectionNumber_def, ← pullback_comp, eulerDegree_pullback_of_isIso e.hom he] at hd
      exact hd
    rw [hL]
    exact (g.eulerDegree_fiber_eq_of_isClosed (k := k) hs _).trans hdeg

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
