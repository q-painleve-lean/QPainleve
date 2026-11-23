/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.EulerCharacteristic

import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus

/-!
# Effectivity from cohomology

A positive Euler characteristic through degree two and vanishing second cohomology
give a nonzero section of a line bundle and hence an effective Cartier divisor.
-/

public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open LineBundleClass

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- If the Euler characteristic through degree two is positive and `H²(X, L)` vanishes,
there is an effective Cartier ideal of class `L⁻¹`. -/
theorem exists_effectiveCartier_of_eulerCharBelow_pos (L : InvertibleSheaf X)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] (hχ : 0 < eulerCharBelow k (mk L) 3)
    (hL₂ : Subsingleton (Cohomology L.obj 2)) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      mk hI.toInvertibleSheaf = (mk L)⁻¹ := by
  let : Subsingleton (Cohomology L.obj 2) := hL₂
  have h₂ : Module.finrank k (Cohomology L.obj 2) = 0 := Module.finrank_zero_of_subsingleton
  have hs : ∃ s : Γ(L.obj, ⊤), s ≠ 0 := by
    by_contra! hz
    have : Subsingleton Γ(L.obj, ⊤) := (subsingleton_iff_forall_eq 0).mpr hz
    have h₀ : Module.finrank k (Cohomology L.obj 0) = 0 :=
      (finrank_cohomology_zero_eq_finrank_globalSections k L.obj).trans
        Module.finrank_zero_of_subsingleton
    rw [eulerCharBelow_mk, Scheme.Modules.eulerCharBelow_succ,
      Scheme.Modules.eulerCharBelow_two, h₀, h₂] at hχ
    omega
  obtain ⟨s, hs⟩ := hs
  exact L.exists_isEffectiveCartier_of_ne_zero s hs

end TauCeti.AlgebraicGeometry.InvertibleSheaf
