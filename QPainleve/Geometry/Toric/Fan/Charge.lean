/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray

import Mathlib.LinearAlgebra.StdBasis

/-!
# Toric boundary charges

The charge map of a labeled family of boundary rays assigns the primitive generator of
each ray to the corresponding basis vector.
-/

public noncomputable section

namespace TauCeti.Toric.Fan

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- The charges of a finite family of centers on toric boundary rays. The charge of a
basis vector is the primitive generator of its assigned ray. -/
def rayChargeMap [Finite ι] (s : ι → Φ.Ray) : (ι → ℤ) →ₗ[ℤ] N :=
  Module.piEquiv ι ℤ N fun j ↦ (s j).primitiveGenerator

/-- A standard basis vector maps to the generator of the ray for its label. -/
@[simp]
theorem rayChargeMap_single [Finite ι] [DecidableEq ι] (s : ι → Φ.Ray) (j : ι) :
    rayChargeMap s (Pi.single j 1) = (s j).primitiveGenerator := by
  rw [rayChargeMap, Module.piEquiv, ← Pi.basisFun_apply, Module.Basis.constr_basis]

end TauCeti.Toric.Fan
