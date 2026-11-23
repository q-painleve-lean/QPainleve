/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# Spreading out sections at valuation-ring stalks

A dominant generic section of a universally closed morphism locally of finite type
extends to a neighbourhood of each valuation-ring stalk of the integral target.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If a universally closed morphism locally of finite type has a dominant generic section,
it has a dominant section over a neighbourhood of each valuation-ring stalk of its
integral target. -/
theorem exists_dominant_section_over_open_of_valuationRing [IsIntegral Y] [UniversallyClosed f]
    [LocallyOfFiniteType f] (y : Y) [ValuationRing (Y.presheaf.stalk y)]
    (s : Spec Y.functionField ⟶ X) [IsDominant s]
    (hs : s ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (g : U.toScheme ⟶ X), g ≫ f = U.ι ∧ IsDominant g := by
  have hsq : s ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ Y.fromSpecStalk y := by
    rw [hs, ← SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
    rfl
  let sq : ValuativeCommSq f :=
    { R := Y.presheaf.stalk y
      domain := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
      valuationRing := ‹ValuationRing (Y.presheaf.stalk y)›
      K := Y.functionField
      i₁ := s
      i₂ := Y.fromSpecStalk y
      commSq := ⟨hsq⟩ }
  have hvc := ((UniversallyClosed.eq_valuativeCriterion.le _ _ f inferInstance).1) sq
  let l := hvc.exists_lift.some
  obtain ⟨U, hy, g, hl, hg⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f (x := y) l.l (by simpa using l.fac_right)
  let i := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ U.fromSpecStalkOfMem y hy
  have he : i ≫ g = s := by
    dsimp only [i]
    rw [Category.assoc, ← hl]
    exact l.fac_left
  have : IsDominant (i ≫ g) := he.symm ▸ ‹IsDominant s›
  exact ⟨U, hy, g, by simpa using hg, IsDominant.of_comp i g⟩

end AlgebraicGeometry.Scheme.Hom
