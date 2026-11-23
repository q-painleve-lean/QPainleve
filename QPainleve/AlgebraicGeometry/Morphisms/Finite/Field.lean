/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Closed points of finite schemes over a field

A finite scheme over a field is locally Artinian, so every point is closed.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every point of a finite scheme over a field is closed. -/
theorem isClosed_singleton_of_isFinite_toSpec {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] (x : X) : IsClosed ({x} : Set X) := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  exact isClosed_singleton

end AlgebraicGeometry.Scheme.Hom
