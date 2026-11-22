/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Orders of constants in scheme function fields

A unit of the base ring has order zero at every point. On an affine scheme,
its image in the function field is represented by the corresponding constant global section.
-/

public section

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

variable {k : Type u} [CommRing k]

/-- A unit of the base ring has order zero because its image is a unit in each stalk. -/
theorem ord_algebraMap_base_unit (X : Scheme) [X.Over (Spec (.of k))]
    [IsIntegral X] [IsLocallyNoetherian X] (c : kˣ) (x : X) :
    X.ord (algebraMap k X.functionField (c : k)) x = 0 := by
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk x) X.functionField]
  exact X.ord_algebraMap_eq_zero_of_isUnit (c.isUnit.map (algebraMap k _))

/-- A base scalar in the function field of an affine scheme is the rational germ of the
corresponding constant global section. -/
theorem Spec.algebraMap_functionField_base (R : Type u) [CommRing R] [IsDomain R]
    [Algebra k R] (c : k) :
    algebraMap k (Spec (.of R)).functionField c =
      ((ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).germToFunctionField ⊤) (algebraMap k R c) := by
  rw [algebraMap_functionField_eq_baseRingToFunctionField, baseRingToFunctionField_apply,
    Modules.baseRingToGlobalSections_apply, specOverSpec_over]
  have h := ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R))
  exact congrArg ((Spec (.of R)).germToFunctionField ⊤) (congr($h c)).symm

end AlgebraicGeometry.Scheme
