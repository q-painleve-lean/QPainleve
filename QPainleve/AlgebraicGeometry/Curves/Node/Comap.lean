/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Étale inverse images of nodal closed subschemes

The inverse image of a nodal closed subscheme under an étale map of ambient
schemes is nodal over the same base.
-/

public section

open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne

/-- Pullback of a nodal closed subscheme along an étale map of the ambient schemes. -/
theorem comap_of_etale {X Y S : Scheme} {D : X.IdealSheafData} {s : X ⟶ S}
    (h : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s)) (f : Y ⟶ X) [Etale f] :
    AtWorstNodalOfRelativeDimensionOne ((D.comap f).subschemeι ≫ f ≫ s) := by
  let j := subschemeMap (D.comap f) D f (D.le_map_comap f)
  have hp : IsPullback (D.comap f).subschemeι j f D.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [j]) (by simp)
  have : Etale j := MorphismProperty.of_isPullback hp inferInstance
  rw [hp.w_assoc]
  exact h.comp_of_etale j

end TauCeti.AlgebraicGeometry.AtWorstNodalOfRelativeDimensionOne
