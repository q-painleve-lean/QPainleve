/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic

import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Strict transforms along successive blowups

The iterated strict transform of a closed subscheme is the scheme-theoretic closure
of its inverse image off both exceptional divisors.

The strict-transform convention and comparison under composition are from the
[Stacks Project, Definition 31.34.1](https://stacks.math.columbia.edu/tag/080D) and
[Lemma 31.34.6](https://stacks.math.columbia.edu/tag/080I).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- In a sequence of two blowups, the iterated strict transform is the
scheme-theoretic closure of the total transform restricted to the common
complement of the two total exceptional divisors. The second center can be
any closed subscheme of the first blowup. -/
theorem ker_blowupMap_ker_blowupMap (I D : X.IdealSheafData) (J : I.blowup.IdealSheafData) :
    let f := J.blowupToBase ≫ I.blowupToBase
    let W := J.blowupToBase ⁻¹ᵁ J.support.compl ⊓ f ⁻¹ᵁ I.support.compl
    (J.blowupMap (I.blowupMap D.subschemeι).ker.subschemeι).ker =
      ((D.comap f).comap W.ι).map W.ι := by
  let p := J.blowupToBase
  let U := I.blowupToBase ⁻¹ᵁ I.support.compl
  let V := p ⁻¹ᵁ J.support.compl
  let W := V ⊓ p ⁻¹ᵁ U
  let v : W.toScheme ⟶ V.toScheme := J.blowup.homOfLE inf_le_left
  let w : W.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := J.blowup.homOfLE inf_le_right
  let c := V.ι ≫ p
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have : IsIso (p ∣_ J.support.compl) := J.isIso_blowupToBase_restrict_compl_support
  have : IsOpenImmersion c := by
    dsimp only [c, V]
    rw [← morphismRestrict_ι]
    infer_instance
  have hpb : IsPullback v (w ≫ p ∣_ U) c U.ι :=
    (isPullback_opens_inf V (p ⁻¹ᵁ U)).paste_vert (isPullback_morphismRestrict p U).flip
  have hv : v ≫ V.ι = W.ι := Scheme.homOfLE_ι _ _
  have hc : (w ≫ p ∣_ U) ≫ U.ι = W.ι ≫ p := by
    rw [← hpb.w]
    dsimp only [c]
    rw [← Category.assoc, hv]
  calc
    _ = ((((D.comap I.blowupToBase).comap U.ι).map U.ι).comap c).map V.ι := by
      rw [ker_blowupMap_subschemeι_eq_map_comap, ker_blowupMap_subschemeι_eq_map_comap,
        compl_support_comap, compl_support_comap]
      simp only [← comap_comp, c, U, V, p]
    _ = ((((D.comap I.blowupToBase).comap U.ι).comap (w ≫ p ∣_ U)).map v).map V.ι := by
      rw [comap_map_of_isPullback_of_isOpenImmersion _ hpb]
    _ = ((D.comap (p ≫ I.blowupToBase)).comap W.ι).map W.ι := by
      rw [← map_comp, hv, ← comap_comp, hc]
      simp only [← comap_comp, Category.assoc]
    _ = _ := by
      dsimp only [W, U, V, p]
      rw [Scheme.Hom.comp_preimage]

end AlgebraicGeometry.Scheme.IdealSheafData
