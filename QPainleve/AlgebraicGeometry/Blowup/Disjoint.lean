/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Blowups at disjoint centers

Blowing up two disjoint closed subschemes, taking the scheme-theoretic inverse image
of the second center after the first blowup, gives the fiber product of the two original
blowups. Thus either order gives the same scheme with its projections to the two
one-step blowups.

The proof uses Tau Ceti's `Scheme.IdealSheafData.blowupLift` and
`Scheme.IdealSheafData.isIso_blowupToBase_restrict_compl_support` for the
universal property and the isomorphism away from the center
(Stacks Project, Tags 0806 and 02OS).
-/

public section

noncomputable section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The blowup comparison is cartesian exactly when the center pulls back to an
effective Cartier divisor on the fiber product. -/
theorem isPullback_blowupMap_iff (I : X.IdealSheafData) (g : Y ⟶ X) :
    IsPullback (I.comap g).blowupToBase (I.blowupMap g) g I.blowupToBase ↔
      ((I.comap g).comap (pullback.fst g I.blowupToBase)).IsEffectiveCartier := by
  constructor
  · intro h
    rw [← h.isoPullback_inv_fst, comap_comp]
    exact (I.comap g).isEffectiveCartier_comap_blowupToBase.comap _
  · intro h
    let lift := (I.comap g).blowupLift (pullback.fst g I.blowupToBase) h
    have hfst : lift ≫ (I.comap g).blowupToBase = pullback.fst g I.blowupToBase :=
      blowupLift_blowupToBase _ _ _
    have hcomp : lift ≫ I.blowupBaseChangeHom g = 𝟙 _ := by
      apply I.pullback_blowupToBase_hom_ext g
      · simp [hfst]
      · rwa [Category.assoc, blowupBaseChangeHom_fst_assoc, reassoc_of% hfst, comap_comp]
    have hIso : IsIso (I.blowupBaseChangeHom g) :=
      ⟨lift, (cancel_mono (I.blowupBaseChangeHom g)).mp (by simp [Category.assoc, hcomp]), hcomp⟩
    exact IsPullback.of_iso_pullback ⟨(I.blowupMap_blowupToBase g).symm⟩
      (asIso (I.blowupBaseChangeHom g)) (I.blowupBaseChangeHom_fst g)
      (I.blowupBaseChangeHom_snd g)

variable (I J : X.IdealSheafData)

/-- If the centers are disjoint, blowing up the inverse image of the first center on
the blowup of the second is the fiber product of their blowups over the original scheme. -/
theorem isPullback_blowupMap_of_disjoint
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    IsPullback (I.comap J.blowupToBase).blowupToBase (I.blowupMap J.blowupToBase)
      J.blowupToBase I.blowupToBase := by
  rw [isPullback_blowupMap_iff, ← comap_comp, pullback.condition, comap_comp]
  let p := pullback.fst J.blowupToBase I.blowupToBase
  let q := pullback.snd J.blowupToBase I.blowupToBase
  have hbase : p ≫ J.blowupToBase = q ≫ I.blowupToBase := pullback.condition
  apply isEffectiveCartier_of_forall_exists_isOpenImmersion
  intro x
  by_cases hx : I.blowupToBase (q x) ∈ I.support
  · -- Over the complement of the second center, projection to the first blowup is open.
    let U : X.Opens := J.support.compl
    let j := (J.blowupToBase ⁻¹ᵁ U).ι
    let w := pullback.fst p j
    have hj : IsOpenImmersion (j ≫ J.blowupToBase) := by
      have : IsIso (J.blowupToBase ∣_ U) := J.isIso_blowupToBase_restrict_compl_support
      rw [← morphismRestrict_ι]
      infer_instance
    have hwq : IsOpenImmersion (w ≫ q) :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback p j).paste_horiz
          (IsPullback.of_hasPullback J.blowupToBase I.blowupToBase).flip).flip hj
    refine ⟨_, w, inferInstance, ?_, ?_⟩
    · rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
      exact fun hxJ ↦ Set.disjoint_left.mp h hx (by
        simpa only [← Scheme.Hom.comp_apply, hbase] using hxJ)
    · rw [← comap_comp]
      exact I.isEffectiveCartier_comap_blowupToBase.comap (w ≫ q)
  · -- Away from the first center, its ideal pulls back to the unit ideal.
    let z := q ≫ I.blowupToBase
    let V := z ⁻¹ᵁ I.support.compl
    refine ⟨_, V.ι, inferInstance, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    rw [← comap_comp, ← comap_comp, Category.assoc,
      (I.comap_eq_top_iff (V.ι ≫ z)).mpr (by
        rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self])]
    exact isEffectiveCartier_top _

/-- The canonical interchange of the two orders of blowup at disjoint centers. -/
def blowupCommOfDisjoint (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    (J.comap I.blowupToBase).blowup ≅ (I.comap J.blowupToBase).blowup :=
  (J.isPullback_blowupMap_of_disjoint I h.symm).isoIsPullback _ _
    (I.isPullback_blowupMap_of_disjoint J h).flip

/-- The interchange preserves the projection to the blowup of the first center. -/
@[reassoc (attr := simp)]
theorem blowupCommOfDisjoint_hom_blowupMap
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    (I.blowupCommOfDisjoint J h).hom ≫ I.blowupMap J.blowupToBase =
      (J.comap I.blowupToBase).blowupToBase := by
  simp [blowupCommOfDisjoint]

/-- The interchange preserves the projection to the blowup of the second center. -/
@[reassoc (attr := simp)]
theorem blowupCommOfDisjoint_hom_blowupToBase
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    (I.blowupCommOfDisjoint J h).hom ≫ (I.comap J.blowupToBase).blowupToBase =
      J.blowupMap I.blowupToBase := by
  simp [blowupCommOfDisjoint]

/-- A center disjoint from the blowup center lifts isomorphically, with the closed
subscheme structure given by the inverse-image ideal. -/
theorem isIso_subschemeMap_blowupToBase_of_disjoint
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    IsIso (subschemeMap (I.comap J.blowupToBase) I J.blowupToBase
      (I.le_map_comap _)) := by
  let U : X.Opens := J.support.compl
  have hrange : Set.range I.subschemeι ⊆ Set.range U.ι := by
    rw [range_subschemeι, Scheme.Opens.range_ι]
    exact fun _ hx hxJ ↦ Set.disjoint_left.mp h hx hxJ
  let i := IsOpenImmersion.lift U.ι I.subschemeι hrange
  have hi : i ≫ U.ι = I.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hrest : IsIso (J.blowupToBase ∣_ U) := J.isIso_blowupToBase_restrict_compl_support
  have hp := IsPullback.of_hasPullback (J.blowupToBase ∣_ U) i
  have : IsIso (pullback.snd (J.blowupToBase ∣_ U) i) :=
    hp.isIso_snd_of_isIso
  have hsmall := hp.paste_horiz (isPullback_morphismRestrict J.blowupToBase U).flip
  rw [hi] at hsmall
  set m := subschemeMap (I.comap J.blowupToBase) I J.blowupToBase (I.le_map_comap _)
  have hbig : IsPullback (I.comap J.blowupToBase).subschemeι m J.blowupToBase I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (subschemeMap_subschemeι _ _ _ _).symm (by simp)
  rw [← IsPullback.isoIsPullback_hom_snd _ _ hbig hsmall]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
