/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Normalization.IsIso
public import TauCeti.AlgebraicGeometry.Scheme.Normal

import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Extending generic lifts along integral morphisms

The normalization of a normal integral scheme in its own function field is an
isomorphism. Mathlib's relative normalization universal property extends a generic
lift along an integral morphism to the entire normal source scheme.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The normalization of a normal integral scheme in its function field is an isomorphism. -/
theorem isIso_fromNormalization_fromSpecStalk_genericPoint (X : Scheme.{u}) [IsIntegral X]
    [IsNormalScheme X] : IsIso (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _) fun x ↦ ?_
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  exact ⟨U, hx, isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed hU⟩

namespace Hom

/-- A generic lift of a map from a normal integral scheme along an integral morphism
extends uniquely over the scheme. -/
theorem existsUnique_lift_of_isIntegralHom {X Y Z : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    (f : X ⟶ Z) (p : Y ⟶ Z) [IsIntegralHom p] (s : Spec X.functionField ⟶ Y)
    (hs : s ≫ p = X.fromSpecStalk (genericPoint X) ≫ f) :
    ∃! g : X ⟶ Y, g ≫ p = f ∧ X.fromSpecStalk (genericPoint X) ≫ g = s := by
  let a := X.fromSpecStalk (genericPoint X)
  let l := pullback.lift a s hs.symm
  let π := pullback.fst f p
  let q := pullback.snd f p
  have hl : a = l ≫ π := (pullback.lift_fst _ _ _).symm
  have := X.isIso_fromNormalization_fromSpecStalk_genericPoint
  have : IsIntegralHom π := inferInstanceAs (IsIntegralHom (pullback.fst f p))
  let d := a.normalizationDesc l π hl
  have hd : d ≫ π = a.fromNormalization := a.normalizationDesc_comp l π hl
  have hq : d ≫ q ≫ p = a.fromNormalization ≫ f := by
    rw [← pullback.condition, ← Category.assoc, hd]
  let g := inv a.fromNormalization ≫ d ≫ q
  have hg : g ≫ p = f := by
    simp only [g, Category.assoc, hq, IsIso.inv_hom_id_assoc]
  have hga : a ≫ g = s := by
    have ha : a ≫ inv a.fromNormalization = a.toNormalization := by
      apply (cancel_mono a.fromNormalization).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        a.toNormalization_fromNormalization]
    calc
      a ≫ g = (a ≫ inv a.fromNormalization) ≫ d ≫ q := by simp only [g, Category.assoc]
      _ = l ≫ q := by rw [ha, a.toNormalization_normalizationDesc_assoc l π hl]
      _ = s := pullback.lift_snd _ _ _
  refine ⟨g, ⟨hg, hga⟩, fun g' ⟨hg', hga'⟩ ↦ ?_⟩
  exact ext_of_isDominant_of_isSeparated p (hg'.trans hg.symm) a (hga'.trans hga.symm)

end Hom

end AlgebraicGeometry.Scheme
