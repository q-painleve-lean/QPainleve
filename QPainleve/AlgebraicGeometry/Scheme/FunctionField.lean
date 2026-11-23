/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Pullback of regular functions on affine integral schemes

Pullback on the generic stalks of affine integral schemes extends the map on
their coordinate rings.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Equal dominant morphisms induce equal pullbacks on the generic stalk. -/
theorem functionFieldMap_congr {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    f.functionFieldMap = g.functionFieldMap := by
  subst g
  rfl

/-- Pullback of a regular affine function agrees with the map on coordinate rings. -/
@[simp]
theorem functionFieldMap_SpecMap_algebraMap {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (f : R ⟶ S) [IsDominant (Spec.map f)] (x : R) :
    (Spec.map f).functionFieldMap (algebraMap R (Spec R).functionField x) =
      algebraMap S (Spec S).functionField (f x) := by
  have h := (Spec.map f).SpecMap_functionFieldMap_fromSpecStalk
  rw [Spec.fromSpecStalk_eq, Spec.fromSpecStalk_eq, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at h
  exact ConcreteCategory.congr_hom h x

end AlgebraicGeometry.Scheme.Hom
