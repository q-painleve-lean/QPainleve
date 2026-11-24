/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# Scheme-theoretic images under open restriction

An ideal pushed forward along a quasi-compact morphism can be computed after
restriction to an open. Restricting a closed immersion to an open whose inverse
image is schematically dense leaves its scheme-theoretic image unchanged. Taking a reduced
closed subscheme commutes with open restriction.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- Forming the scheme-theoretic image of a closed subscheme under a quasi-compact morphism
commutes with restriction to an open of the target. -/
theorem comap_map_of_isPullback_of_isOpenImmersion {Y W Y' W' : Scheme.{u}}
    (D : Y.IdealSheafData) {j : Y ⟶ W} [QuasiCompact j]
    {c : W' ⟶ W} [IsOpenImmersion c] {j' : Y' ⟶ W'} {e : Y' ⟶ Y}
    (sq : IsPullback j' e c j) :
    (D.map j).comap c = (D.comap e).map j' := by
  have hs := (IsPullback.of_hasPullback e D.subschemeι).paste_horiz sq
  unfold IdealSheafData.map
  rw [← ker_eq_comap_of_isPullback_of_isOpenImmersion c hs,
    ← D.comapIso_hom_fst e, Category.assoc,
    Scheme.Hom.ker_comp_of_isIso (D.comapIso e).hom]

/-- A closed immersion and its restriction to a schematically dense inverse image of an open
have the same scheme-theoretic image in the original ambient scheme. -/
theorem map_comap_ker_of_isSchemeTheoreticallyDominant {Z X : Scheme.{u}}
    (q : Z ⟶ X) [IsClosedImmersion q] (U : X.Opens)
    [IsSchemeTheoreticallyDominant ((q ⁻¹ᵁ U).ι)] :
    (q.ker.comap U.ι).map U.ι = q.ker := by
  rw [← ker_eq_comap_of_isPullback q (isPullback_morphismRestrict q U), ← Scheme.Hom.ker_comp,
    morphismRestrict_ι, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]

/-- An isomorphism pulls back the scheme-theoretic union of two closed subschemes
to the union of their pullbacks. -/
@[simp]
theorem comap_inf_of_isIso {X Y : Scheme.{u}} (I J : Y.IdealSheafData)
    (f : X ⟶ Y) [IsIso f] : (I ⊓ J).comap f = I.comap f ⊓ J.comap f := by
  refine le_antisymm (le_inf (comap_mono f inf_le_left) (comap_mono f inf_le_right)) ?_
  let K := I.comap f ⊓ J.comap f
  have hK : K.comap (inv f) ≤ I ⊓ J := by
    apply le_inf
    · simpa only [← comap_comp, IsIso.inv_hom_id, comap_id] using
        comap_mono (inv f) (inf_le_left : K ≤ I.comap f)
    · simpa only [← comap_comp, IsIso.inv_hom_id, comap_id] using
        comap_mono (inv f) (inf_le_right : K ≤ J.comap f)
  simpa only [← comap_comp, IsIso.hom_inv_id, comap_id] using comap_mono f hK

/-- If an ideal sheaf pulls back to the unit ideal along a dominant morphism, the
open complement of its support is dense. -/
theorem dense_compl_support_of_comap_eq_top {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (f : Y ⟶ X) [IsDominant f] (h : I.comap f = ⊤) :
    Dense (I.support.compl : Set X) := by
  apply f.denseRange.mono
  rw [Set.range_subset_iff]
  intro y
  exact f.mem_preimage.mp (by rw [(I.comap_eq_top_iff f).mp h]; trivial)

/-- Taking the reduced subscheme commutes with restriction along an open immersion. -/
@[simp]
theorem radical_comap_of_isOpenImmersion {X Y : Scheme.{u}}
    (D : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : (D.comap f).radical = D.radical.comap f := by
  rw [← vanishingIdeal_support (I := D), comap_vanishingIdeal_of_isOpenImmersion,
    ← vanishingIdeal_support (I := D.comap f), support_comap]
  rfl

/-- The reduced inverse image of an invariant closed subscheme under an equivariant
morphism is invariant under the source automorphism. -/
theorem exists_radicalComapSubschemeIso {X Y : Scheme.{u}}
    (D : X.IdealSheafData) (f : Y ⟶ X) {e : X ≅ X} {g : Y ≅ Y}
    {d : D.subscheme ≅ D.subscheme} (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)
    (hf : g.hom ≫ f = f ≫ e.hom) :
    let R := (D.comap f).radical
    ∃ r : R.subscheme ≅ R.subscheme, r.hom ≫ R.subschemeι = R.subschemeι ≫ g.hom := by
  have hpb : IsPullback D.subschemeι d.hom e.hom D.subschemeι :=
    (IsPullback.of_horiz_isIso ⟨hd⟩).flip
  have hD : D.comap e.hom = D := by
    simpa only [ker_subschemeι] using (ker_eq_comap_of_isPullback D.subschemeι hpb).symm
  let R := (D.comap f).radical
  have hR : R.comap g.hom = R := by
    dsimp only [R]
    rw [← radical_comap_of_isOpenImmersion, ← comap_comp, hf, comap_comp, hD]
  let r := R.subschemeMap R g.hom (le_map_iff_comap_le.mpr hR.le)
  have hr : r ≫ R.subschemeι = R.subschemeι ≫ g.hom := subschemeMap_subschemeι _ _ _ _
  have hpull : IsPullback R.subschemeι r g.hom R.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ hr.symm
      (by simpa only [ker_subschemeι] using hR)
  have : IsIso r := hpull.isIso_snd_of_isIso
  exact ⟨asIso r, hr⟩

end AlgebraicGeometry.Scheme.IdealSheafData
