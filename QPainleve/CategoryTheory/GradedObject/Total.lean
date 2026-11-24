/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Isomorphisms of total objects

In a category with zero morphisms, each component of a graded map is an
arrow retract of its map on the coproduct of all components. This is the
retract argument used in Tau Ceti's `quasiIsoAt_sigmaMap_iff`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.GradedObject

variable (I : Type) (C : Type*) [Category C] [HasCoproducts.{0} C] [HasZeroMorphisms C]

/-- A graded morphism is an isomorphism if its map on the total objects is an
isomorphism. Each component is a retract by the coproduct inclusion and projection. -/
instance : (total I C).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    classical
    have (i : I) : IsIso (f i) := by
      let s := Limits.Sigma.map (g := A) (f := B) (fun j : I ↦ f j)
      have hs : IsIso s := hf
      have hπ : Sigma.π A i ≫ f i = s ≫ Sigma.π B i := by
        apply Sigma.hom_ext
        intro j
        by_cases h : j = i
        · subst j
          simp [s]
        · simp [s, Sigma.ι_π_of_ne_assoc _ h, Sigma.ι_π_of_ne _ h]
      let r : RetractArrow (f i) s :=
        { i := Arrow.homMk (Sigma.ι A i) (Sigma.ι B i) (by simp [s])
          r := Arrow.homMk (Sigma.π A i) (Sigma.π B i) hπ
          retract := by ext <;> simp }
      exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms C) r hs
    exact isIso_of_isIso_apply f

end CategoryTheory.GradedObject
