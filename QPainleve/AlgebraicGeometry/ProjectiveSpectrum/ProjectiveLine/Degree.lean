/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine

import QPainleve.AlgebraicGeometry.Curves.Morphism
import QPainleve.AlgebraicGeometry.Morphisms.ClosedImmersion.Fiber
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Morphisms
import TauCeti.AlgebraicGeometry.Curves.Degree.Pullback
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine

/-!
# Degree-one maps to families of projective lines

A map from a proper integral curve to the projective line is an isomorphism if
it pulls back the tautological line bundle to a bundle of degree one. Over a
base, the same test on closed fibers recognizes the comparison to a reduced
family with polarized projective-line fibers.

The curve argument uses the finite flat degree formula
`LineBundleClass.eulerDegree_pullback_of_finrank_eq`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.Hom

local notation "𝒪₁(" k ")" =>
  LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) 1)

/-- A morphism from a proper integral curve over a field to the projective line
is an isomorphism if the pullback of `𝒪(1)` has degree one. -/
theorem isIso_of_eulerDegree_pullback_twistingSheaf_eq_one
    {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
    (f : C ⟶ projectiveLine k) [f.IsOver (Spec (.of k))]
    (h : eulerDegree k (pullback f (𝒪₁(k))) = 1) : IsIso f := by
  have hnontrivial : pullback f (𝒪₁(k)) ≠ 1 := by
    intro he
    rw [he, eulerDegree_one] at h
    omega
  have : IsDominant f := f.isDominant_of_pullback_twistingSheaf_ne_one hnontrivial
  have : IsFinite f := f.isFinite_of_isDominant_of_isCurveOver (k := k)
  have : IsNoetherian (projectiveLine k) := Scheme.IsCurveOver.isNoetherian k _
  have (y : projectiveLine k) : ValuationRing ((projectiveLine k).presheaf.stalk y) :=
    Scheme.IsCurveOver.valuationRing_stalk k _ y
  have : Flat f := f.flat_of_isDominant_of_valuationRing
  have : RelativeDimensionLE 1 (projectiveLine k ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have hrank := f.finrank_eq_finrank_fieldRange_functionFieldMap
  have hdegree : eulerDegree k (𝒪₁(k)) = 1 := by
    rw [eulerDegree_mk]
    exact projectiveLine.eulerDegree_twistingSheaf k 1
  rw [eulerDegree_pullback_of_finrank_eq k f hrank, hdegree, mul_one] at h
  refine (f.isIso_iff_finrank_eq).mpr ?_
  ext y
  simpa only [Pi.one_apply, hrank y] using Int.natCast_inj.mp h

/-- A proper map into a quasi-compact reduced Jacobson family of polarized
projective lines is an isomorphism if the pullback of the polarization has
degree one on each closed fiber and the source fibers are proper integral
curves. The target structure map must send closed points to closed points. -/
theorem isIso_of_eulerDegree_pullback_closed_fibers_eq_one
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsProper f] [CompactSpace Y] [JacobsonSpace Y] [IsReduced Y]
    (hg : Set.MapsTo g (closedPoints Y) (closedPoints S)) (L : LineBundleClass Y)
    (hY : ∀ s : S, IsClosed ({s} : Set S) →
      ∃ e : projectiveLine (S.residueField s) ≅ g.fiber s,
        e.hom ≫ g.fiberToSpecResidueField s =
          (projectiveLine (S.residueField s) ↘ Spec (.of (S.residueField s))) ∧
        pullback e.hom (pullback (g.fiberι s) L) = 𝒪₁(S.residueField s))
    (hX : ∀ s : S, IsClosed ({s} : Set S) →
      let := (f ≫ g).fiberOverSpecResidueField s
      ((f ≫ g).fiber s).IsCurveOver (S.residueField s))
    (hL : ∀ s : S, IsClosed ({s} : Set S) →
      let := (f ≫ g).fiberOverSpecResidueField s
      eulerDegree (S.residueField s) (pullback ((f ≫ g).fiberι s) (pullback f L)) = 1) :
    IsIso f := by
  refine f.isIso_of_isIso_fiberCompMap_of_isClosed g hg fun s hs ↦ ?_
  let := (f ≫ g).fiberOverSpecResidueField s
  have : ((f ≫ g).fiber s).IsCurveOver (S.residueField s) := hX s hs
  obtain ⟨e, he, htwist⟩ := hY s hs
  let φ := f.fiberCompMap g s
  let ψ := φ ≫ e.inv
  have : ψ.IsOver (Spec (.of (S.residueField s))) := ⟨by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]
    exact f.fiberCompMap_fiberToSpecResidueField g s⟩
  have hψ : ψ ≫ e.hom = φ := by simp [ψ]
  have hp : pullback ψ (𝒪₁(S.residueField s)) =
      pullback ((f ≫ g).fiberι s) (pullback f L) := by
    rw [← htwist, pullback_comp ψ e.hom, hψ, pullback_comp φ,
      f.fiberCompMap_fiberι, ← pullback_comp]
  have : IsIso ψ :=
    ψ.isIso_of_eulerDegree_pullback_twistingSheaf_eq_one (hp.symm ▸ hL s hs)
  exact IsIso.of_isIso_comp_right φ e.inv

end AlgebraicGeometry.Scheme.Hom
