/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import Mathlib.AlgebraicGeometry.Noetherian

import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType

/-!
# Ideal sheaves of finite type

On a locally Noetherian scheme every ideal sheaf is of finite type.
-/

public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Every ideal sheaf on a locally Noetherian scheme is of finite type. -/
theorem isFiniteType_sheaf {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    I.sheaf.IsFiniteType := by
  refine Scheme.Modules.isFiniteType_of_finite_sections I.sheaf fun U hU ↦ ?_
  have := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : Γ(I.sheaf, U) →ₗ[Γ(X, U)] Γ(X, U) := ((Scheme.Modules.sectionsFunctor U).map I.sheafι).hom
  exact Module.Finite.of_injective φ (I.sheafι_app_injective U)

end AlgebraicGeometry.Scheme.IdealSheafData
