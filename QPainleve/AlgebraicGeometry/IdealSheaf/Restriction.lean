/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

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

/-- Taking the reduced subscheme commutes with restriction along an open immersion. -/
@[simp]
theorem radical_comap_of_isOpenImmersion {X Y : Scheme.{u}}
    (D : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : (D.comap f).radical = D.radical.comap f := by
  rw [← vanishingIdeal_support (I := D), comap_vanishingIdeal_of_isOpenImmersion,
    ← vanishingIdeal_support (I := D.comap f), support_comap]
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData
