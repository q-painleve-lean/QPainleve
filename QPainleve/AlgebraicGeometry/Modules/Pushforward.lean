/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Direct image along a morphism with one-point image

A module with vanishing global sections has zero direct image along a morphism
whose underlying map has image contained in a point.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

open Scheme.Modules

universe u

/-- A sheaf of modules with vanishing global sections pushes forward to zero along
a morphism with constant underlying map. -/
theorem isZero_pushforward_of_constant {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    (y : Y) (hf : ∀ x, f x = y) [Subsingleton Γ(M, ⊤)] :
    IsZero ((pushforward f).obj M) := by
  let N := (pushforward f).obj M
  apply (IsZero.iff_id_eq_zero N).mpr
  apply Scheme.Modules.hom_ext
  intro U
  have : Subsingleton Γ(N, U) := by
    dsimp only [N]
    rw [pushforward_obj_obj]
    by_cases hy : y ∈ U
    · have htop : f ⁻¹ᵁ U = ⊤ := eq_top_iff.mpr fun x _ ↦ f.mem_preimage.mpr (hf x ▸ hy)
      rw [htop]
      infer_instance
    · have hbot : f ⁻¹ᵁ U = ⊥ :=
        eq_bot_iff.mpr fun x hx ↦ (hy (hf x ▸ f.mem_preimage.mp hx)).elim
      rw [hbot]
      exact Module.subsingleton Γ(X, (⊥ : X.Opens)) _
  exact ConcreteCategory.hom_ext _ _ fun _ ↦ Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Hom
