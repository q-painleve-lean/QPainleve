/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Stalk

import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Stalks of ideal sheaves

The stalk of an arbitrary sum is the sum of the stalk ideals. Its order of vanishing
is the infimum of the orders of the summands. We also compare stalk ideals in a
commutative square of closed subschemes.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- An ideal sheaf is determined by its pullbacks to the spectra of the local rings. -/
theorem eq_of_comap_fromSpecStalk_eq {I J : X.IdealSheafData}
    (h : ∀ x : X, I.comap (X.fromSpecStalk x) = J.comap (X.fromSpecStalk x)) : I = J := by
  have hlocal (R : Type u) [CommRing R] [IsLocalRing R] (g : Spec (.of R) ⟶ X) :
      I.comap g = J.comap g := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk g, comap_comp, comap_comp, h]
  exact le_antisymm (le_of_comap_Spec_isLocalRing fun R _ _ g ↦ (hlocal R g).le)
    (le_of_comap_Spec_isLocalRing fun R _ _ g ↦ (hlocal R g).ge)

/-- The stalk ideal of a sum is the sum of the stalk ideals. -/
@[simp]
theorem stalkIdeal_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkIdeal x = ⨆ i, (I i).stalkIdeal x := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (TopologicalSpace.Opens.mem_top x)
  simp only [stalkIdeal_eq_map _ ⟨U, hU⟩ x hxU, ideal_iSup, iSup_apply, Ideal.map_iSup]

/-- The order of a sum is the infimum of the orders of its summands. -/
@[simp]
theorem stalkOrder_iSup {ι : Type*} (I : ι → X.IdealSheafData) (x : X) :
    (⨆ i, I i).stalkOrder x = ⨅ i, (I i).stalkOrder x := by
  simp only [stalkOrder_def, stalkIdeal_iSup, Ideal.localOrder_iSup]

variable {Y : Scheme.{u}}

/-- Extending an ideal along a scheme morphism can only increase its stalk order. -/
theorem stalkOrder_le_comap (J : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    J.stalkOrder (f x) ≤ (J.comap f).stalkOrder x := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  rw [J.natCast_le_stalkOrder_iff] at hn
  rw [natCast_le_stalkOrder_iff, stalkIdeal_comap]
  let φ := (f.stalkMap x).hom
  refine (Ideal.map_mono (f := φ) hn).trans ?_
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) _

/-- An isomorphism on local rings preserves the order of an inverse-image ideal. -/
theorem stalkOrder_comap_of_isIso_stalkMap (J : Y.IdealSheafData)
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    (J.comap f).stalkOrder x = J.stalkOrder (f x) := by
  rw [stalkOrder_def, stalkIdeal_comap, J.stalkOrder_def]
  exact Ideal.localOrder_map_equiv _ (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- In a commutative square of closed subschemes, if the induced map of closed subschemes
is an isomorphism and the ambient stalk map at a point of the source subscheme is an isomorphism,
then the inverse-image ideal and the source ideal have the same stalk at that point. -/
theorem stalkIdeal_comap_eq_of_isIso_stalkMap (J : Y.IdealSheafData) {I : X.IdealSheafData}
    (f : X ⟶ Y) (g : I.subscheme ⟶ J.subscheme)
    (w : I.subschemeι ≫ f = g ≫ J.subschemeι) [IsIso g] (z : I.subscheme)
    [IsIso (f.stalkMap (I.subschemeι z))] :
    (J.comap f).stalkIdeal (I.subschemeι z) = I.stalkIdeal (I.subschemeι z) := by
  have hy : f (I.subschemeι z) = J.subschemeι (g z) := congr($(w) z)
  let c := (Y.presheaf.stalkCongr (.of_eq hy)).hom
  have hc : f.stalkMap (I.subschemeι z) ≫ I.subschemeι.stalkMap z =
      (c ≫ J.subschemeι.stalkMap (g z)) ≫ g.stalkMap z := by
    have h := Scheme.Hom.stalkMap_congr_hom _ _ w z
    simp only [Scheme.Hom.stalkMap_comp] at h
    exact h.trans (Category.assoc c (J.subschemeι.stalkMap (g z)) (g.stalkMap z)).symm
  have hker := congrArg (fun a : Y.presheaf.stalk (f (I.subschemeι z)) ⟶
    I.subscheme.presheaf.stalk z ↦ RingHom.ker a.hom) hc
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (g.stalkMap z)).injective,
    CommRingCat.hom_comp, ← RingHom.comap_ker, ← RingHom.comap_ker,
    I.subschemeι.ker_stalkMap_of_isClosedImmersion, J.subschemeι.ker_stalkMap_of_isClosedImmersion,
    ker_subschemeι, ker_subschemeι] at hker
  have htransport {y y' : Y} (h : y = y') :
      (J.stalkIdeal y').comap (Y.presheaf.stalkCongr (.of_eq h)).hom.hom = J.stalkIdeal y := by
    subst y'
    simp
  unfold c at hker
  rw [htransport hy] at hker
  rw [stalkIdeal_comap, ← hker, Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.stalkMap (I.subschemeι z))).surjective]

end AlgebraicGeometry.Scheme.IdealSheafData
