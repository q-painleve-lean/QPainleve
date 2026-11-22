/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Function field pullback along dominant rational maps

A dominant rational map of integral schemes restricts to a map from the generic point of the
source into the generic point of the target. The resulting map on generic stalks determines
the rational map. The construction uses Mathlib's generic-point restriction of rational maps
and TauCeti's `Scheme.Hom.genericPoint_eq_of_isDominant`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X Y : Scheme}

/-- The generic-point restriction of a dominant rational map is dominant. -/
instance [IrreducibleSpace X] (f : X ⤏ Y) [f.IsDominant] : IsDominant f.fromFunctionField := by
  obtain ⟨p, rfl⟩ := f.exists_rep
  have : IsDominant p.hom := p.isDominant_toRationalMap_iff.mp inferInstance
  rw [fromFunctionField_toRationalMap]
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  have h : IsDominant (p.domain.fromSpecStalkOfMem (genericPoint X)
      ((genericPoint_specializes _).mem_open p.domain.2 p.dense_domain.nonempty.choose_spec) ≫
        p.domain.ι) := by
    rw [Opens.fromSpecStalkOfMem_ι]
    infer_instance
  have := IsDominant.of_comp_of_isOpenImmersion _ _ (H := h)
  infer_instance

variable [IsIntegral X] [IrreducibleSpace Y]

/-- The restriction of a dominant rational map to the generic point lands at the generic point. -/
theorem fromFunctionField_closedPoint (f : X ⤏ Y) [f.IsDominant] :
    f.fromFunctionField (IsLocalRing.closedPoint X.functionField) = genericPoint Y := by
  rw [← f.fromFunctionField.genericPoint_eq_of_isDominant]
  congr 1
  exact Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _

/-- Pullback from the generic stalk of the target along a dominant rational map. -/
def functionFieldMap (f : X ⤏ Y) [f.IsDominant] : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq f.fromFunctionField_closedPoint) ≫
    stalkClosedPointTo f.fromFunctionField

/-- The function field pullback recovers the restriction to the generic point. -/
@[reassoc]
theorem specMap_functionFieldMap (f : X ⤏ Y) [f.IsDominant] :
    Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField := by
  rw [functionFieldMap, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
    Spec_stalkClosedPointTo_fromSpecStalk]

/-- Dominant rational maps from an integral scheme agree exactly when their pullbacks agree. -/
theorem functionFieldMap_eq_iff (f g : X ⤏ Y) [f.IsDominant] [g.IsDominant] :
    f.functionFieldMap = g.functionFieldMap ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst g; rfl⟩
  exact f.eq_of_fromFunctionField_eq g (by rw [← f.specMap_functionFieldMap,
    ← g.specMap_functionFieldMap, h])

end AlgebraicGeometry.Scheme.RationalMap
