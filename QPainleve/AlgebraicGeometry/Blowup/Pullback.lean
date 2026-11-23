/-
Copyright (c) 2026 Yuma Mizuno and the QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus

/-!
# Base change of a blowup near its center

The base-change comparison is cartesian if the pulled-back center is already an
effective Cartier divisor on the fiber product. In particular, it is cartesian when
the base change is an isomorphism over the support of the center.
This uses Tau Ceti's universal property of blowups and its closed immersion into the fiber
product. See the Stacks Project, [Tag 0806](https://stacks.math.columbia.edu/tag/0806).
-/

public noncomputable section

open CategoryTheory Limits

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

/-- A blowup commutes with base change by a morphism which is an isomorphism over the
support of its center. -/
theorem isPullback_blowupMap_of_support_subset_isoLocus (I : X.IdealSheafData) (g : Y ⟶ X)
    (h : (I.support : Set X) ⊆ g.isoLocus) :
    IsPullback (I.comap g).blowupToBase (I.blowupMap g) g I.blowupToBase := by
  rw [isPullback_blowupMap_iff, ← comap_comp, pullback.condition, comap_comp]
  refine I.isEffectiveCartier_comap_blowupToBase.comap_of_support_subset_isoLocus _ ?_
  refine Set.Subset.trans ?_
    (Scheme.Hom.preimage_isoLocus_le_of_isPullback
      ((IsPullback.of_hasPullback g I.blowupToBase).flip))
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage, Scheme.Hom.coe_preimage]
  exact Set.preimage_mono h

end AlgebraicGeometry.Scheme.IdealSheafData
