/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
import Mathlib.AlgebraicGeometry.FunctionField
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Generic points of closed subschemes

The image of the generic point of an irreducible closed subscheme has closure equal to the
support. For an integral closed subscheme, the vanishing ideal of this closure recovers its
defining ideal sheaf.
At that point the stalk ideal is the maximal ideal of the ambient local ring.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme} (I : X.IdealSheafData)

/-- An irreducible closed subscheme has support the closure of the image of its generic point. -/
theorem support_eq_closure_subschemeι_genericPoint [IrreducibleSpace I.subscheme] :
    (I.support : Set X) = closure {I.subschemeι (genericPoint I.subscheme)} := by
  have h := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
  rw [Set.image_univ, I.range_subschemeι, I.support.isClosed.closure_eq] at h
  exact h.def.symm

/-- The vanishing ideal of the closure of the generic point of an integral closed subscheme is its
ideal sheaf. -/
theorem vanishingIdeal_closure_subschemeι_genericPoint [IsIntegral I.subscheme] :
    vanishingIdeal ⟨closure {I.subschemeι (genericPoint I.subscheme)}, isClosed_closure⟩ = I := by
  have h : (⟨closure {I.subschemeι (genericPoint I.subscheme)}, isClosed_closure⟩ :
      Closeds X) = I.support :=
    SetLike.coe_injective I.support_eq_closure_subschemeι_genericPoint.symm
  rw [h, vanishingIdeal_support]
  exact I.isReduced_subscheme_iff_radical_eq.mp inferInstance

/-- The stalk ideal at the generic point of an integral closed subscheme is the maximal
ideal of the ambient local ring. -/
@[simp] theorem stalkIdeal_subschemeι_genericPoint [IsIntegral I.subscheme] :
    I.stalkIdeal (I.subschemeι (genericPoint I.subscheme)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι (genericPoint I.subscheme))) := by
  simpa only [I.subschemeι.ker_stalkMap_of_isClosedImmersion, I.ker_subschemeι] using
    IsLocalRing.ker_eq_maximalIdeal (K := I.subscheme.functionField) _
      (I.subschemeι.stalkMap_surjective (genericPoint I.subscheme))

end AlgebraicGeometry.Scheme.IdealSheafData
