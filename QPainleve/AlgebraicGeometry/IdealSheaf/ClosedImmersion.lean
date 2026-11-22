/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Ideal sheaves of closed integral subschemes

The kernel ideal of a closed immersion from an integral scheme is the vanishing ideal
of the closure of the image of its generic point.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The ideal of a closed integral subscheme is the vanishing ideal of the closure of the
image of its generic point. -/
public theorem ker_eq_vanishingIdeal_closure_genericPoint {C X : Scheme.{u}} (i : C ⟶ X)
    [IsClosedImmersion i] [IsIntegral C] :
    i.ker = IdealSheafData.vanishingIdeal
      ⟨closure {i (genericPoint C)}, isClosed_closure⟩ := by
  have hp := (genericPoint_spec C).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at hp
  have hs : i.ker.support = ⟨closure {i (genericPoint C)}, isClosed_closure⟩ := by
    apply SetLike.coe_injective
    rw [i.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq, ← hp]
    rfl
  have : IsReduced i.ker.subscheme := isReduced_of_isOpenImmersion (CategoryTheory.inv i.toImage)
  have hi := (IdealSheafData.isReduced_subscheme_iff_radical_eq i.ker).mp ‹_›
  rw [← hi, ← IdealSheafData.vanishingIdeal_support, hs]

end AlgebraicGeometry.Scheme.Hom
