/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Residue fields at closed points over a field

The residue-field extension at a closed point of a scheme locally of finite type
over a field is finite. This is the form of the Nullstellensatz for the native
algebra structure on the residue field.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The residue field of a closed point on a scheme locally of finite type
over a field is finite over the base field. -/
theorem moduleFinite_residueField_of_isClosed {k : Type u} [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    {x : X} (hx : IsClosed ({x} : Set X)) :
    Module.Finite k (X.residueField x) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : IsFinite (X.fromSpecResidueField x ≫ X ↘ Spec (.of k)) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rwa [Scheme.fromSpecResidueField_comp_over, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finite_algebraMap] at h

end AlgebraicGeometry.Scheme
