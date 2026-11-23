/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.FunctionField
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import QPainleve.AlgebraicGeometry.RationalMap.Composition
import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Descent of rational maps along modifications

A rational map on a modification of an integral scheme comes from a unique rational
map on the base. Restricting the modification to the open where it is an isomorphism
gives the inverse to precomposition.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A rational map from the source of a modification descends uniquely along it. -/
theorem existsUnique_rationalMap_comp_eq_of_isModification (f : X ⟶ Y) [IsModification f]
    (r : X ⤏ Z) : ∃! q : Y ⤏ Z, f.toRationalMap.comp q = r := by
  obtain ⟨U, hU, hV, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  let V := f ⁻¹ᵁ U
  have : Nonempty V := Set.nonempty_coe_sort.mpr hV.nonempty
  have : Nonempty U := Set.nonempty_coe_sort.mpr hU.nonempty
  have : IsDominant V.ι := Opens.isDominant_ι hV
  have : IsDominant U.ι := Opens.isDominant_ι hU
  let p : Y.PartialMap X := ⟨U, hU, inv (f ∣_ U) ≫ V.ι⟩
  have : IsDominant p.hom := inferInstanceAs (IsDominant (inv (f ∣_ U) ≫ V.ι))
  have : p.toRationalMap.IsDominant := p.isDominant_toRationalMap_iff.mpr ‹IsDominant p.hom›
  have hinv : f.toRationalMap.comp p.toRationalMap = RationalMap.id X := by
    apply RationalMap.comp_left_injective V.ι.toRationalMap
    dsimp only
    have hf : V.ι.toRationalMap.comp f.toRationalMap =
        (f ∣_ U).toRationalMap.comp U.ι.toRationalMap := by
      simp only [RationalMap.comp_toRationalMap, toRationalMap_compHom, morphismRestrict_ι, V]
    calc
      _ = ((f ∣_ U).toRationalMap.comp U.ι.toRationalMap).comp p.toRationalMap := by
        simp only [← RationalMap.comp_assoc, hf]
      _ = (f ∣_ U).toRationalMap.comp p.hom.toRationalMap := by
        rw [RationalMap.comp_assoc, ← p.hom_toRationalMap_eq_comp]
      _ = _ := by
        simp only [RationalMap.comp_toRationalMap, toRationalMap_compHom, p,
          IsIso.hom_inv_id_assoc, Category.comp_id]
  have hcomp : f.toRationalMap.comp (p.toRationalMap.comp r) = r := by
    simp only [← RationalMap.comp_assoc, hinv, RationalMap.id_comp]
  exact ⟨p.toRationalMap.comp r, hcomp, fun q hq ↦
    RationalMap.comp_left_injective f.toRationalMap (hq.trans hcomp.symm)⟩

end AlgebraicGeometry.Scheme.Hom
