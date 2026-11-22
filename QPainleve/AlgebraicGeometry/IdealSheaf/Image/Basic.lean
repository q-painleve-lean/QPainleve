/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Image

/-!
# Vanishing of image ideal sheaves

The image ideal sheaf of a morphism to the structure sheaf detects whether
the morphism is zero.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- An image ideal sheaf is zero exactly when its defining morphism is zero. -/
@[simp]
theorem imageIdealSheaf_eq_bot_iff {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    φ.imageIdealSheaf = ⊥ ↔ φ = 0 := by
  constructor
  · intro h
    ext U s
    have hs := φ.app_mem_imageIdealSheaf_sections U s
    rw [h, Scheme.IdealSheafData.sections_bot] at hs
    exact (Ideal.mem_bot (R := Γ(X, U))).mp hs
  · rintro rfl
    ext U r
    rw [imageIdealSheaf_ideal, mem_imageIdeal, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      Ideal.mem_bot]
    exact ⟨fun ⟨_, hr⟩ ↦ hr.symm, fun hr ↦ ⟨0, hr.symm⟩⟩

end AlgebraicGeometry.Scheme.Modules.Hom
