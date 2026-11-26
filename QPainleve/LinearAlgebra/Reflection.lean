/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Reflection

/-!
# Reflections on quotients

A module reflection induces the identity modulo the span of its reflecting vector.
-/

public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {x : M} {f : M →ₗ[R] R}

/-- A reflection fixes every class in the quotient by the span of its reflecting vector. -/
@[simp high]
theorem mkQ_reflection_apply (h : f x = 2) (y : M) :
    (R ∙ x).mkQ (reflection h y) = (R ∙ x).mkQ y := by
  rw [reflection_apply, map_sub, sub_eq_self, ← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Module
