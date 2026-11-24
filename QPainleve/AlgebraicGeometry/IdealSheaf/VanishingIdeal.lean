/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Reduced closed subsets under closed immersions

The reduced subscheme on a closed subset of a closed subscheme is also reduced
when viewed as a closed subscheme of the ambient scheme.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- The reduced inverse image depends only on the reduced closed subscheme. -/
@[simp]
theorem radical_comap_radical {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.radical.comap f).radical = (I.comap f).radical := by
  rw [← vanishingIdeal_support, ← vanishingIdeal_support (I := I.comap f),
    support_comap, support_comap, support_radical]

/-- The ideal of a reduced point closure at a specialization is the prime of the ambient
local ring corresponding to the given generization. -/
theorem stalkIdeal_vanishingIdeal_closure_singleton_of_specializes {X : Scheme.{u}}
    {η x : X} (h : η ⤳ x) :
    (vanishingIdeal ⟨closure {η}, isClosed_closure⟩).stalkIdeal x =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
        (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [stalkIdeal_eq_map _ ⟨U, hU⟩ x hxU]
  exact map_ideal_vanishingIdeal_closure_singleton_of_specializes hxU h

/-- The ambient vanishing ideal of the image of a closed subset pulls back to the
vanishing ideal of that subset along a closed immersion. -/
theorem comap_vanishingIdeal_image_of_isClosedImmersion {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (Z : Closeds Y) :
    (vanishingIdeal ⟨i '' (Z : Set Y), i.isClosedEmbedding.isClosedMap _ Z.isClosed⟩).comap i =
      vanishingIdeal Z := by
  let I := vanishingIdeal Z
  let g := I.subschemeι ≫ i
  have : IsClosedImmersion g := inferInstanceAs (IsClosedImmersion (I.subschemeι ≫ i))
  have : IsReduced g.ker.subscheme := isReduced_of_isOpenImmersion (asIso g.toImage).inv
  have hs : (g.ker.support : Set X) = i '' (Z : Set Y) := by
    rw [g.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq]
    have hg : ⇑g = i ∘ I.subschemeι :=
      funext (Scheme.Hom.comp_apply I.subschemeι i)
    have hr : Set.range g = i '' Set.range I.subschemeι := hg ▸ Set.range_comp _ _
    rw [hr, range_subschemeι, coe_support_vanishingIdeal]
  have hrad : g.ker.radical = g.ker := (isReduced_subscheme_iff_radical_eq _).mp ‹_›
  have hI : vanishingIdeal ⟨i '' (Z : Set Y), i.isClosedEmbedding.isClosedMap _ Z.isClosed⟩ =
      g.ker := by
    exact (congrArg vanishingIdeal (Closeds.ext hs.symm)).trans
      (vanishingIdeal_support.trans hrad)
  rw [hI, Scheme.Hom.comap_ker_comp_of_isClosedImmersion, ker_subschemeι]

/-- Along a closed immersion, the reduced ideal of an image point restricts to the
reduced ideal of the corresponding point, including for nonclosed points. -/
@[simp]
theorem comap_vanishingIdeal_closure_singleton_of_isClosedImmersion
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (x : Y) :
    (vanishingIdeal ⟨closure {i x}, isClosed_closure⟩).comap i =
      vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
  let Z : Closeds Y := ⟨closure {x}, isClosed_closure⟩
  have hZ : (⟨i '' (Z : Set Y), i.isClosedEmbedding.isClosedMap _ Z.isClosed⟩ : Closeds X) =
      ⟨closure {i x}, isClosed_closure⟩ :=
    Closeds.ext ((i.isClosedEmbedding.closure_image_eq {x}).symm.trans
      (congrArg closure (Set.image_singleton (f := i) (a := x))))
  simpa only [hZ] using comap_vanishingIdeal_image_of_isClosedImmersion i Z

end AlgebraicGeometry.Scheme.IdealSheafData
