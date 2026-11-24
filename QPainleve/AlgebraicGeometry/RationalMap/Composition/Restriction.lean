/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined

import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Composing with a regular representative

A morphism through the domain of a partial representative computes composition
on its whole source, including when the morphism has nondense image.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A morphism factoring through the domain of a representative can be followed
by its rational map. The composite is represented by ordinary composition with
the defining morphism. -/
theorem exists_compOfDefined_eq_of_lift {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsReduced Y] [Y.IsSeparated] [Z.IsSeparated]
    (f : X ⟶ Y) (p : Y.PartialMap Z) (l : X ⟶ p.domain.toScheme) (hl : l ≫ p.domain.ι = f) :
    ∃ h : f.toRationalMap.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈
        p.toRationalMap.domain,
      f.toRationalMap.compOfDefined p.toRationalMap h = (l ≫ p.hom).toRationalMap := by
  obtain ⟨h, he⟩ := f.toRationalMap.fromFunctionField_compOfDefined_of_rep p
    (X.fromSpecStalk (genericPoint X) ≫ l)
    (by simp [RationalMap.fromFunctionField_toRationalMap, hl])
  exact ⟨h, RationalMap.eq_of_fromFunctionField_eq _ _
    (by simpa [RationalMap.fromFunctionField_toRationalMap] using he)⟩

/-- Pullback of a defined composite along a dominant morphism is regular if the
resulting morphism to the intermediate scheme factors through a representative. -/
theorem comp_compOfDefined_eq_of_lift {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [X.IsSeparated] [IsReduced Y] [Y.IsSeparated] [Z.IsSeparated]
    (f : W ⟶ X) [IsDominant f] (g : X ⟶ Y) (p : Y.PartialMap Z)
    (h : g.toRationalMap.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈
      p.toRationalMap.domain)
    (l : W ⟶ p.domain.toScheme) (hl : l ≫ p.domain.ι = f ≫ g) :
    f.toRationalMap.comp (g.toRationalMap.compOfDefined p.toRationalMap h) =
      (l ≫ p.hom).toRationalMap := by
  obtain ⟨_, he⟩ := f.toRationalMap.comp_compOfDefined g.toRationalMap p.toRationalMap h
  obtain ⟨_, hl'⟩ := (f ≫ g).exists_compOfDefined_eq_of_lift p l hl
  simpa only [RationalMap.comp_toRationalMap, toRationalMap_compHom, hl'] using he.symm

/-- A lift of a dense open through a partial representative computes the regular
representative of its composite with a dominant morphism. -/
theorem comp_eq_toRationalMap_of_lift {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated] [Z.IsSeparated]
    (f : X ⟶ Y) [IsDominant f] (p : Y.PartialMap Z)
    (W : X.Opens) (hW : Dense (W : Set X)) (l : W.toScheme ⟶ p.domain.toScheme)
    (hl : l ≫ p.domain.ι = W.ι ≫ f) :
    f.toRationalMap.comp p.toRationalMap =
      (⟨W, hW, l ≫ p.hom⟩ : X.PartialMap Z).toRationalMap := by
  let : Nonempty W := Set.nonempty_coe_sort.mpr hW.nonempty
  have : IsDominant W.ι := Opens.isDominant_ι hW
  apply RationalMap.comp_left_injective W.ι.toRationalMap
  dsimp only
  have h := f.toRationalMap.fromFunctionField_mem_domain_of_isDominant p.toRationalMap
  rw [← f.toRationalMap.compOfDefined_eq_comp p.toRationalMap h,
    W.ι.comp_compOfDefined_eq_of_lift f p h l hl]
  exact PartialMap.hom_toRationalMap_eq_comp (⟨W, hW, l ≫ p.hom⟩ : X.PartialMap Z)

end AlgebraicGeometry.Scheme.Hom
