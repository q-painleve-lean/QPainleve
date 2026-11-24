/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.IsSepClosed

import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Connected schemes over a separably closed field

The projections from field extensions have geometrically irreducible fibers, so
connectedness over a separably closed field is geometric.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.GeometricallyConnected

universe u

/-- A scheme over a separably closed field is geometrically connected if and only if its
underlying space is connected. -/
theorem iff_connectedSpace_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyConnected f ↔ ConnectedSpace X := by
  refine ⟨fun _ ↦ connectedSpace_of_subsingleton f, fun h ↦ ⟨?_⟩⟩
  intro K _ y Z p q hsq
  have : GeometricallyIrreducible y := inferInstance
  have : GeometricallyIrreducible p := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : UniversallyOpen y := inferInstance
  have : UniversallyOpen p := MorphismProperty.of_isPullback hsq.flip inferInstance
  exact connectedSpace p p.isOpenMap

end AlgebraicGeometry.GeometricallyConnected
