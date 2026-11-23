/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

/-!
# Scheme-theoretic images over a base

The factorization through the scheme-theoretic image of a morphism over a base
uses the induced structure morphism on the image closed subscheme.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map to the scheme-theoretic image is a morphism over the base. -/
instance isOver_toImage {C X S : Scheme.{u}} [C.Over S] [X.Over S]
    (i : C ⟶ X) [i.IsOver S] : i.toImage.IsOver S := by
  constructor
  rw [IdealSheafData.over_eq_subschemeι_comp, ← Category.assoc, toImage_imageι]
  exact comp_over i S

end AlgebraicGeometry.Scheme.Hom
