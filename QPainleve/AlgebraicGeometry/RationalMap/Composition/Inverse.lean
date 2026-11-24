/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined

/-!
# Inverting a rational commutative square

An invertible horizontal map reverses a fixed-fiber evaluation square once the
inverse X map is defined at the generic value of the target evaluation.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {X Y A B : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsReduced A] [IsIntegral B]
  [Y.IsSeparated] [A.IsSeparated] [B.IsSeparated]

variable [IsIntegral A]

/-- Reverse a rational evaluation square with an isomorphism on the source side
and inverse dominant rational maps on the target side. The inverse square uses
the domain condition on the target evaluation. -/
theorem compOfDefined_eq_inv_comp_of_comp_eq
    (a : X ⤏ A) (b : Y ⤏ B) (e : X ≅ Y) (f : A ⤏ B) [f.IsDominant] (g : B ⤏ A)
    (hfg : f.comp g = id A)
    (ha : a.fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈ f.domain)
    (hb : b.fromFunctionField (IsLocalRing.closedPoint Y.functionField) ∈ g.domain)
    (h : a.compOfDefined f ha = e.hom.toRationalMap.comp b) :
    b.compOfDefined g hb = e.inv.toRationalMap.comp a := by
  obtain ⟨hb', hleft⟩ := e.hom.toRationalMap.comp_compOfDefined b g hb
  have ha' := h.symm ▸ hb'
  obtain ⟨hc, hright⟩ := a.compOfDefined_comp f g ha ha'
  have hcomp : (e.hom.toRationalMap.comp b).compOfDefined g hb' =
      (a.compOfDefined f ha).compOfDefined g ha' := by
    simp only [h]
  apply e.hom.toRationalMap.comp_left_injective
  calc
    _ = (e.hom.toRationalMap.comp b).compOfDefined g hb' := hleft.symm
    _ = (a.compOfDefined f ha).compOfDefined g ha' := hcomp
    _ = a := by
      rw [hright]
      simpa only [hfg] using a.compOfDefined_id (hfg ▸ hc)
    _ = e.hom.toRationalMap.comp (e.inv.toRationalMap.comp a) := by
      simp only [← comp_assoc, comp_toRationalMap, Hom.toRationalMap_compHom, e.hom_inv_id]
      exact (id_comp a).symm

end AlgebraicGeometry.Scheme.RationalMap
