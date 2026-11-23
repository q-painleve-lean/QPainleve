/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
public import QPainleve.AlgebraicGeometry.Blowup.Isomorphism
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

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

/-- The kernel defining the strict transform of a closed immersion agrees with the one
computed using the canonical closed subscheme of its ideal. -/
theorem ker_blowupMap_eq_ker_blowupMap_subschemeι {D X : Scheme.{u}}
    (I : X.IdealSheafData) (i : D ⟶ X) [IsClosedImmersion i] :
    (I.blowupMap i).ker = (I.blowupMap i.ker.subschemeι).ker := by
  let e := asIso i.toImage
  have he : e.hom ≫ i.ker.subschemeι = i := i.toImage_imageι
  let J := I.comap i.ker.subschemeι
  have hJ : J.comap e.hom = I.comap i := by rw [← I.comap_comp, he]
  let g := J.blowupIso e hJ
  have hcomp : g.hom ≫ I.blowupMap i.ker.subschemeι = I.blowupMap i := by
    apply I.eq_blowupMap
    dsimp only [g, J]
    rw [Category.assoc, blowupMap_blowupToBase, blowupIso_hom_blowupToBase_assoc, he]
  rw [← hcomp, Scheme.Hom.ker_comp_of_isIso]

/-- The intersection of the strict-transform ideal and the exceptional ideal equals
their product. The strict-transform ideal is saturated with respect to the locally
principal exceptional ideal. -/
theorem inf_ker_blowupMap_subschemeι_exceptional {X : Scheme.{u}} (I D : X.IdealSheafData) :
    (I.blowupMap D.subschemeι).ker ⊓ I.comap I.blowupToBase =
      (I.blowupMap D.subschemeι).ker * I.comap I.blowupToBase := by
  let S := (I.blowupMap D.subschemeι).ker
  let E := I.comap I.blowupToBase
  change S ⊓ E = S * E
  let j := Scheme.Opens.ι (E.support.compl)
  have hS : S = ((D.comap I.blowupToBase).comap j).map j :=
    ker_blowupMap_subschemeι_eq_map_comap I D
  have hEj : E.comap j = ⊤ :=
    (comap_eq_top_iff _ _).mpr (Scheme.Opens.ι_preimage_self _)
  rw [inf_eq_colon_mul _ _ I.isEffectiveCartier_comap_blowupToBase.locallyPrincipal]
  congr 1
  apply le_antisymm _ (le_colon _ _)
  have hcomap : ((S.colon E) * E).comap j ≤ S.comap j :=
    comap_mono j (colon_mul_le S E)
  rw [comap_mul, hEj, ← one_eq_top, mul_one] at hcomap
  have ht : S.comap j ≤ (D.comap I.blowupToBase).comap j := by
    rw [hS]
    exact comap_map_le _ _
  exact ((le_map_iff_comap_le).mpr (hcomap.trans ht)).trans_eq hS.symm

/-- Restricting the strict transform to an open of the blowup computes the
scheme-theoretic closure of the restricted total transform off the exceptional divisor. -/
theorem comap_ker_blowupMap_subschemeι_eq_map_comap_of_isOpenImmersion
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I D : X.IdealSheafData) {Y : Scheme.{u}} (j : Y ⟶ I.blowup) [IsOpenImmersion j] :
    let V := j ⁻¹ᵁ (I.comap I.blowupToBase).support.compl
    (I.blowupMap D.subschemeι).ker.comap j =
      ((D.comap (j ≫ I.blowupToBase)).comap V.ι).map V.ι := by
  let U := (I.comap I.blowupToBase).support.compl
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  dsimp only
  rw [ker_blowupMap_subschemeι_eq_map_comap,
    comap_map_of_isPullback_of_isOpenImmersion _ (isPullback_morphismRestrict j U).flip]
  simp only [← comap_comp, U, morphismRestrict_ι_assoc]

/-- Strict-transform ideals commute with restriction to an open subscheme of the base. -/
theorem comap_ker_blowupMap_subschemeι_blowupMap_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (I D : X.IdealSheafData)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (I.blowupMap D.subschemeι).ker.comap (I.blowupMap f) =
      ((I.comap f).blowupMap (D.comap f).subschemeι).ker := by
  rw [comap_ker_blowupMap_subschemeι_eq_map_comap_of_isOpenImmersion,
    ker_blowupMap_subschemeι_eq_map_comap, blowupMap_blowupToBase, comap_comp D,
    ← compl_support_comap, comap_comap_blowupMap]

/-- A base isomorphism identifying center ideals carries strict transforms to strict
transforms of the inverse-image ideals. -/
theorem comap_ker_blowupMap_subschemeι_blowupIso {X Y : Scheme.{u}}
    (J D : Y.IdealSheafData) (e : X ≅ Y) {I : X.IdealSheafData} (hI : J.comap e.hom = I) :
    (J.blowupMap D.subschemeι).ker.comap (J.blowupIso e hI).hom =
      (I.blowupMap (D.comap e.hom).subschemeι).ker := by
  let i := (D.comap e.hom).subschemeι
  let d := subschemeMap (D.comap e.hom) D e.hom (D.le_map_comap e.hom)
  have : IsIso (pullback.snd e.hom D.subschemeι) :=
    (IsPullback.of_hasPullback e.hom D.subschemeι).isIso_snd_of_isIso
  have : IsIso d := by
    dsimp only [d]
    rw [← D.comapIso_hom_snd]
    infer_instance
  have hd : d ≫ D.subschemeι = i ≫ e.hom := subschemeMap_subschemeι _ _ _ _
  have hC : (J.comap D.subschemeι).comap d = I.comap i := by
    rw [← comap_comp, hd, comap_comp, hI]
  let f := (J.comap D.subschemeι).blowupIso (asIso d) hC
  have hw : I.blowupMap i ≫ (J.blowupIso e hI).hom = f.hom ≫ J.blowupMap D.subschemeι := by
    apply J.blowup_hom_ext
    · simp only [Category.assoc, blowupIso_hom_blowupToBase,
        blowupMap_blowupToBase_assoc, ← hd, blowupMap_blowupToBase,
        blowupIso_hom_blowupToBase_assoc, f, asIso_hom]
    · simp only [Category.assoc, blowupIso_hom_blowupToBase, blowupMap_blowupToBase_assoc,
        comap_comp, hI]
      exact (I.comap i).isEffectiveCartier_comap_blowupToBase
  rw [← Scheme.Hom.ker_comp_of_isIso f.hom, ← hw,
    Scheme.Hom.comap_ker_comp_of_isClosedImmersion]

/-- On an open disjoint from the exceptional divisor, the strict transform agrees
with the pullback from the base. -/
theorem comap_ker_blowupMap_subschemeι_of_comap_eq_top {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (I D : X.IdealSheafData) (j : Y ⟶ I.blowup) [IsOpenImmersion j]
    (h : I.comap (j ≫ I.blowupToBase) = ⊤) :
    (I.blowupMap D.subschemeι).ker.comap j = D.comap (j ≫ I.blowupToBase) := by
  have hW : j ⁻¹ᵁ (I.comap I.blowupToBase).support.compl = ⊤ := by
    rw [← compl_support_comap, ← comap_comp, h, support_top]
    ext x
    simp
  have : IsIso (Scheme.Opens.ι (⊤ : Y.Opens)) := Y.topIso.isIso_hom
  rw [comap_ker_blowupMap_subschemeι_eq_map_comap_of_isOpenImmersion, hW,
    map_comap_of_isClosedImmersion, Scheme.Hom.ker_eq_bot_of_isIso, sup_bot_eq]

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

/-- On an open of a blowup, a factor of the total transform obtained by removing a power
of the exceptional ideal defines the strict transform if the exceptional complement in
that factor is schematically dense. -/
theorem comap_ker_blowupMap_subschemeι_eq_of_factor {X V Z : Scheme.{u}}
    (I J : X.IdealSheafData) [IsLocallyNoetherian X]
    (c : V ⟶ I.blowup) [IsOpenImmersion c] (q : Z ⟶ V) [IsClosedImmersion q] (n : ℕ)
    (h : J.comap (c ≫ I.blowupToBase) =
      q.ker * (I.comap (c ≫ I.blowupToBase)) ^ n)
    (hd : IsSchemeTheoreticallyDominant
      ((q ⁻¹ᵁ (I.comap (c ≫ I.blowupToBase)).support.compl).ι)) :
    (I.blowupMap J.subschemeι).ker.comap c = q.ker := by
  let E := I.comap I.blowupToBase
  let W : I.blowup.Opens := E.support.compl
  let U : V.Opens := c ⁻¹ᵁ W
  have hU : U = (E.comap c).support.compl := (compl_support_comap E c).symm
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian I.blowupToBase
  have hE : (E.comap c).comap U.ι = ⊤ :=
    (comap_eq_top_iff _ _).mpr (hU ▸ Scheme.Opens.ι_preimage_self U)
  have htotal : ((J.comap I.blowupToBase).comap c).comap U.ι = q.ker.comap U.ι := by
    rw [← comap_comp J c I.blowupToBase, h, comap_mul, comap_pow,
      comap_comp I c I.blowupToBase, hE]
    rw [← one_eq_top, one_pow, mul_one]
  have hcomp : U.ι ≫ c = c ∣_ W ≫ W.ι := (morphismRestrict_ι c W).symm
  let : IsSchemeTheoreticallyDominant ((q ⁻¹ᵁ U).ι) := by
    rw [hU, ← comap_comp]
    exact hd
  rw [ker_blowupMap_subschemeι_eq_map_comap,
    comap_map_of_isPullback_of_isOpenImmersion _ (isPullback_morphismRestrict c W).flip,
    ← comap_comp, ← hcomp, comap_comp, htotal, map_comap_ker_of_isSchemeTheoreticallyDominant]

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
