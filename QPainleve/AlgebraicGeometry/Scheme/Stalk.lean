/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent

/-!
# Stalk algebras over an affine base

On a scheme locally of finite type over an affine base, the canonical base algebra
on a stalk is essentially of finite type.
-/

public section

open CategoryTheory Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical stalk algebra of a scheme locally of finite type over `Spec R` is essentially
of finite type over `R`. -/
theorem essFiniteType_stalk (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] (x : X) :
    Algebra.EssFiniteType R (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let A := Γ(X, U)
  let : Algebra R A := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsScalarTower R A (X.presheaf.stalk x) :=
    isScalarTower_base_section_stalk R X ⟨x, hxU⟩
  have : Algebra.FiniteType R A := finiteType_sections_of_locallyOfFiniteType R X ⟨U, hU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType A (X.presheaf.stalk x) :=
    .of_isLocalization _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact .comp R A _

end AlgebraicGeometry.Scheme
