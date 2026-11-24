/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Pullback

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction

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

open CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- A closed point away from a blowup center pulls back to a reduced closed point. -/
theorem exists_comap_ker_fromSpecResidueField_blowupToBase (J : X.IdealSheafData)
    {p : X} (hp : IsClosed ({p} : Set X)) (h : p ∉ J.support) :
    ∃ q : J.blowup, IsClosed ({q} : Set J.blowup) ∧ J.blowupToBase q = p ∧
      (X.fromSpecResidueField p).ker.comap J.blowupToBase = (J.blowup.fromSpecResidueField q).ker :=
  J.blowupToBase.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp
    J.support.compl
    (by simpa only [← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff] using h)

variable (I J : X.IdealSheafData)

/-- If the centers are disjoint, blowing up the inverse image of the first center on
the blowup of the second is the fiber product of their blowups over the original scheme. -/
theorem isPullback_blowupMap_of_disjoint
    (h : Disjoint (I.support : Set X) (J.support : Set X)) :
    IsPullback (I.comap J.blowupToBase).blowupToBase (I.blowupMap J.blowupToBase)
      J.blowupToBase I.blowupToBase := by
  refine I.isPullback_blowupMap_of_support_subset_isoLocus J.blowupToBase ?_
  have hIJ : (I.support : Set X) ⊆ J.support.compl := fun _ hx ↦ Set.disjoint_left.mp h hx
  exact hIJ.trans
    (J.blowupToBase.le_isoLocus_iff.mpr J.isIso_blowupToBase_restrict_compl_support)

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
