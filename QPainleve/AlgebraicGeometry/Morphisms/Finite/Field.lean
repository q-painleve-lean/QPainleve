/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

import Mathlib.RingTheory.Artinian.Algebra

/-!
# Closed points of finite schemes over a field

The affine algebra of a finite scheme over a field is Artinian, so every
point of the scheme is closed.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Every point of a finite scheme over a field is closed. -/
theorem isClosed_singleton_of_isFinite_toSpec {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] (x : X) : IsClosed ({x} : Set X) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) := f.moduleFinite_appTop rfl
  have : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite k _
  let p : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  have hp := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr
    (IsArtinianRing.isMaximal_of_isPrime _)
  rw [← Set.preimage_image_eq ({x} : Set X) X.isoSpec.hom.homeomorph.injective, Set.image_singleton]
  exact hp.preimage X.isoSpec.hom.continuous

end AlgebraicGeometry.Scheme.Hom
