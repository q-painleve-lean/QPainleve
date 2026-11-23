/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Dominant sections of separated morphisms

A dominant section of a separated morphism with reduced source is its inverse.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A dominant section of a separated morphism with reduced source is its inverse. -/
theorem isIso_of_dominant_section [IsReduced X] [IsSeparated f] (s : Y ⟶ X)
    [IsDominant s] (hs : s ≫ f = 𝟙 Y) : IsIso f := by
  have hinv : f ≫ s = 𝟙 X :=
    ext_of_isDominant_of_isSeparated f (by simp [hs]) s (by simp [reassoc_of% hs])
  exact ⟨⟨s, hinv, hs⟩⟩

end AlgebraicGeometry.Scheme.Hom
