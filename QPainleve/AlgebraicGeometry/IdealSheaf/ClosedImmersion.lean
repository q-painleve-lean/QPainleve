/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Ideal sheaves under closed immersions

The kernel ideal of a closed immersion from an integral scheme is the vanishing ideal
of the closure of the image of its generic point. A closed immersion takes the support
of an ideal sheaf to the support of its scheme-theoretic image.
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

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The support of the image ideal under a closed immersion is the image of the support. -/
public theorem support_map_of_isClosedImmersion {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : X ⟶ Y) [IsClosedImmersion f] :
    ((I.map f).support : Set Y) = f '' (I.support : Set X) := by
  rw [support_map, Closeds.coe_closure]
  exact (f.isClosedEmbedding.isClosedMap _ I.support.isClosed).closure_eq

end AlgebraicGeometry.Scheme.IdealSheafData
