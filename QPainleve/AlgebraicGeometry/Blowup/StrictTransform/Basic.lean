/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension

/-!
# Strict transforms of closed subschemes

If the center restricts to an effective Cartier divisor on a closed subscheme, that
subscheme embeds in the blowup as its own strict transform. The embedding is the
lift given by the universal property, and its kernel is the scheme-theoretic closure
described by Tau Ceti's `ker_blowupMap`. Away from the exceptional divisor, the
strict and total transforms agree.

## References

* The Stacks Project, Lemma 31.34.2 (tag 080E).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The strict transform of a closed subscheme is obtained by restricting its total transform
off the exceptional divisor and taking the scheme-theoretic image in the blowup. -/
theorem ker_blowupMap_subschemeι_eq_map_comap {X : Scheme.{u}} (I J : X.IdealSheafData) :
    let E := I.comap I.blowupToBase
    let W : I.blowup.Opens := E.support.compl
    let j := W.ι
    (I.blowupMap J.subschemeι).ker = ((J.comap I.blowupToBase).comap j).map j := by
  let E := I.comap I.blowupToBase
  let W : I.blowup.Opens := E.support.compl
  let f := pullback.snd J.subschemeι I.blowupToBase
  have hW : f ⁻¹ᵁ W = (pullback.fst J.subschemeι I.blowupToBase ≫ J.subschemeι) ⁻¹ᵁ
      I.support.compl := by
    dsimp only [W, E]
    rw [compl_support_comap, ← Scheme.Hom.comp_preimage, ← pullback.condition]
  have hTotal : f.ker = J.comap I.blowupToBase := by
    simpa [f] using (ker_eq_comap_of_isPullback J.subschemeι
      (IsPullback.of_hasPullback J.subschemeι I.blowupToBase).flip)
  rw [I.ker_blowupMap, ← hW, ← morphismRestrict_ι, Scheme.Hom.ker_comp]
  rw [ker_eq_comap_of_isPullback f (isPullback_morphismRestrict f W), hTotal]

/-- The strict transform agrees with the total transform on the complement of
the exceptional divisor. -/
theorem comap_ker_blowupMap_subschemeι_exceptionalCompl
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I J : X.IdealSheafData) :
    let W : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
    (I.blowupMap J.subschemeι).ker.comap W.ι = (J.comap I.blowupToBase).comap W.ι := by
  let W : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have he := comap_map_of_isOpenImmersion ((J.comap I.blowupToBase).comap W.ι) W.ι
  simpa only [ker_blowupMap_subschemeι_eq_map_comap] using he

variable {D X : Scheme.{u}} (I : X.IdealSheafData) (i : D ⟶ X)

/-- The canonical map from the blowup of the inverse image of the center factors through
the lift of the original scheme when the inverse image of the center is Cartier. -/
@[reassoc]
theorem blowupToBase_comp_blowupLift (h : (I.comap i).IsEffectiveCartier) :
    (I.comap i).blowupToBase ≫ I.blowupLift i h = I.blowupMap i := by
  apply I.eq_blowupMap
  simp

/-- A closed subscheme on which the center is Cartier embeds in the ambient blowup by the
canonical lift. -/
theorem isClosedImmersion_blowupLift [IsClosedImmersion i] (h : (I.comap i).IsEffectiveCartier) :
    IsClosedImmersion (I.blowupLift i h) := by
  have : IsIso (I.comap i).blowupToBase := (isIso_blowupToBase_iff (I.comap i)).mpr h
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (I.comap i).blowupToBase,
    I.blowupToBase_comp_blowupLift i h]
  infer_instance

/-- When the inverse image of the center is Cartier, the lift has the ideal of the
scheme-theoretic strict transform. -/
theorem ker_blowupLift (h : (I.comap i).IsEffectiveCartier) :
    (I.blowupLift i h).ker =
      (Scheme.Opens.ι ((pullback.fst i I.blowupToBase ≫ i) ⁻¹ᵁ I.support.compl) ≫
        pullback.snd i I.blowupToBase).ker := by
  have : IsIso (I.comap i).blowupToBase := (isIso_blowupToBase_iff (I.comap i)).mpr h
  rw [← Scheme.Hom.ker_comp_of_isIso (I.comap i).blowupToBase (I.blowupLift i h),
    I.blowupToBase_comp_blowupLift i h, I.ker_blowupMap]

/-- Restricting the exceptional ideal along the lift recovers the inverse image of the
center on the original scheme. -/
@[simp]
theorem comap_blowupLift_exceptional (h : (I.comap i).IsEffectiveCartier) :
    (I.comap I.blowupToBase).comap (I.blowupLift i h) = I.comap i := by
  rw [← comap_comp, blowupLift_blowupToBase]

end AlgebraicGeometry.Scheme.IdealSheafData
