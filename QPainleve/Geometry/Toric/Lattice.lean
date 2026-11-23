/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic

/-!
# Real extensions of integral lattice equivalences

The real extension of an integral equivalence is a linear equivalence, since the
extension of its inverse is inverse by `IsIntegralLattice.extend_comp`.
-/

public noncomputable section

namespace TauCeti.Toric.IsIntegralLattice

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

/-- Extend an additive equivalence of the integral lattices to their real spaces. -/
def extendEquiv (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i') (e : N ≃+ N') :
    V ≃ₗ[ℝ] V' :=
  LinearEquiv.ofLinearMap (hi.extend i' e) (hi'.extend i e.symm)
    (by simp) (by simp)

/-- The real extension restricts to the given equivalence on integral lattice points. -/
@[simp]
theorem extendEquiv_apply_lattice (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (e : N ≃+ N') (x : N) : hi.extendEquiv hi' e (i x) = i' (e x) := by
  simp [extendEquiv]

end TauCeti.Toric.IsIntegralLattice
