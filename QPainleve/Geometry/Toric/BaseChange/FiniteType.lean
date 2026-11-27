/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan

import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
import TauCeti.Algebra.Group.UniqueProds.Submonoid
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.Algebra.Module.Torsion.Hom

/-!
# Finite type and Noetherianity of toric schemes

Gordan's lemma gives finite algebra generation for the coordinate ring of each chart.
A toric scheme of a finite fan over a Noetherian ring is therefore Noetherian.
-/

public section

open AlgebraicGeometry CategoryTheory Algebra

namespace TauCeti.Toric

universe u

variable (R : Type*) [CommRing R] {N V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} {σ : PointedCone ℝ V}

/-- The coordinate ring of a toric chart over a domain is a domain. -/
instance isDomain_affineChartRing [IsDomain R] (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : IsDomain (affineChartRing R hi σ) :=
  inferInstanceAs (IsDomain (AddMonoidAlgebra R (dualSemigroup hi σ)))

/-- The monomials of a finite generating set of the dual semigroup generate the chart algebra. -/
theorem IsToricCone.finiteType_affineChartRing (hσ : IsToricCone i σ)
    (hi : IsIntegralLattice i) : FiniteType R (affineChartRing R hi σ) := by
  have : AddMonoid.FG (dualSemigroup hi σ) := hσ.fg_dualSemigroup hi
  infer_instance

/-- Over a Noetherian coefficient ring, the coordinate ring of a toric cone is Noetherian. -/
theorem IsToricCone.isNoetherianRing_affineChartRing [IsNoetherianRing R]
    (hσ : IsToricCone i σ) (hi : IsIntegralLattice i) : IsNoetherianRing (affineChartRing R hi σ) :=
  have := hσ.finiteType_affineChartRing R hi
  FiniteType.isNoetherianRing R _

namespace Fan

variable {R N : Type u} [CommRing R] {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-- The structure morphism of a toric scheme is locally of finite type. -/
instance locallyOfFiniteType_finiteFanSchemeToSpec :
    LocallyOfFiniteType (Φ.finiteFanSchemeToSpec R) := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFiniteType.{u}) (Φ.affineChartOpenCover R)).2
  intro σ
  let cone : Φ.cones := σ
  suffices LocallyOfFiniteType (Φ.affineChartι R cone ≫ Φ.finiteFanSchemeToSpec R) from this
  rw [Φ.affineChartι_finiteFanSchemeToSpec R cone, Spec.algebraMap,
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
    RingHom.finiteType_algebraMap]
  exact (Φ.isToricCone cone.property).finiteType_affineChartRing R Φ.lattice

/-- A toric scheme over a Noetherian coefficient ring is locally Noetherian. -/
instance isLocallyNoetherian_finiteFanScheme [IsNoetherianRing R] :
    IsLocallyNoetherian (Φ.finiteFanScheme R) :=
  (isLocallyNoetherian_iff_openCover (Φ.affineChartOpenCover R)).2 fun σ ↦ by
    let cone : Φ.cones := σ
    rw [Φ.affineChartOpenCover_X R cone]
    exact isLocallyNoetherian_Spec.2
      ((Φ.isToricCone cone.property).isNoetherianRing_affineChartRing R Φ.lattice)

/-- A toric scheme of a finite fan over a Noetherian coefficient ring is Noetherian. -/
instance isNoetherian_finiteFanScheme [IsNoetherianRing R] :
    IsNoetherian (Φ.finiteFanScheme R) := by
  let : Finite (Φ.affineChartOpenCover R).I₀ := inferInstanceAs (Finite Φ.cones)
  let : ∀ σ, CompactSpace ((Φ.affineChartOpenCover R).X σ) := fun σ ↦ by
    rw [Φ.affineChartOpenCover_X R σ]
    infer_instance
  exact { toIsLocallyNoetherian := inferInstance
          toCompactSpace := (Φ.affineChartOpenCover R).compactSpace }

end Fan

end TauCeti.Toric
