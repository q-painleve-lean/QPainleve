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

A morphism from a reduced scheme gives its scheme-theoretic image the reduced structure.
This gives a factorization through a reduced closed section when the image lies in that section.
The kernel ideal of a closed immersion from an integral scheme is the vanishing ideal
of the closure of the image of its generic point. A closed immersion takes the support
of an ideal sheaf to the support of its scheme-theoretic image.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A reduced source determines the reduced scheme structure on its schematic image. -/
public theorem ker_eq_vanishingIdeal_support {X Y : Scheme} (f : X ⟶ Y) [IsReduced X] :
    f.ker = IdealSheafData.vanishingIdeal f.ker.support :=
  le_antisymm (by rw [IdealSheafData.vanishingIdeal_support]; exact f.ker.le_radical)
    (IdealSheafData.vanishingIdeal_le_ker_of_range_subset f f.range_subset_ker_support)

/-- A map from a reduced scheme with image in a reduced closed section factors
as its map to the base followed by the section. -/
public theorem eq_comp_of_range_subset_of_section {C T S : Scheme} [IsReduced C] [IsReduced S]
    (a : C ⟶ T) (q : T ⟶ S) (r : S ⟶ T) [IsClosedImmersion r] (hr : r ≫ q = 𝟙 S)
    (ha : Set.range a ⊆ Set.range r) : a = a ≫ q ≫ r := by
  have hker : r.ker ≤ a.ker := by
    rw [r.ker_eq_vanishingIdeal_support]
    exact IdealSheafData.vanishingIdeal_le_ker_of_range_subset a
      (ha.trans r.range_subset_ker_support)
  let b := IsClosedImmersion.lift r a hker
  have hba : b ≫ r = a := IsClosedImmersion.lift_fac _ _ _
  have hb : b = a ≫ q := by simp only [← hba, Category.assoc, hr, Category.comp_id]
  simpa only [Category.assoc] using hba.symm.trans (congrArg (· ≫ r) hb)

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
