/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Ramification
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Ramification
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Ramification of closed point blowup towers

The Jacobian ideal of the composite from a tower of point blowups of a smooth surface
is the product of the total transforms of the exceptional ideals. Thus it is effective
Cartier, including in a tower with infinitely near points.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- The ramification ideal of the projection of a closed point tower, using
the structure map to the field induced by the tower. -/
def ramificationIdealSheafToBase (hT : IsClosedPointTower X T) : Y.IdealSheafData := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
  have : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : Smooth (Y ↘ Spec (.of k)) := (hT.smoothOfRelativeDimension (X ↘ Spec (.of k))).smooth
  exact ramificationIdealSheaf k T.toBase

/-- The tower ideal is the native ramification ideal for its composite projection. -/
theorem ramificationIdealSheafToBase_def (hT : IsClosedPointTower X T) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
    haveI : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
    haveI : Smooth (Y ↘ Spec (.of k)) :=
      (hT.smoothOfRelativeDimension (X ↘ Spec (.of k))).smooth
    hT.ramificationIdealSheafToBase k = ramificationIdealSheaf k T.toBase := (rfl)

/-- The ramification ideal of a closed point tower pulls back to that of a specified morphism
identified with its projection by a source isomorphism. -/
theorem comap_ramificationIdealSheafToBase (hT : IsClosedPointTower X T)
    {W : Scheme.{u}} [W.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (W ↘ Spec (.of k))]
    (e : W ≅ Y) {f : W ⟶ X} [f.IsOver (Spec (.of k))] (he : e.hom ≫ T.toBase = f) :
    letI := SmoothOfRelativeDimension.smooth 2 (W ↘ Spec (.of k))
    (hT.ramificationIdealSheafToBase k).comap e.hom = ramificationIdealSheaf k f := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ X ↘ Spec (.of k)⟩
  have : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : e.hom.IsOver (Spec (.of k)) := ⟨((reassoc_of% he) _).trans (comp_over f _)⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    hT.smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 2 (W ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 2 (Y ↘ Spec (.of k))
  calc
    _ = ramificationIdealSheaf k (e.hom ≫ T.toBase) := by
      rw [ramificationIdealSheaf_comp k e.hom T.toBase 2,
        ramificationIdealSheaf_eq_top_of_isOpenImmersion, top_mul,
        ramificationIdealSheafToBase_def]
    _ = _ := ramificationIdealSheaf_congr k he

/-- The projection of the empty point tower has unit ramification ideal. -/
@[simp]
theorem ramificationIdealSheafToBase_nil :
    (IsClosedPointTower.nil (X := X)).ramificationIdealSheafToBase k = ⊤ := by
  rw [ramificationIdealSheafToBase_def]
  have : IsOpenImmersion (BlowupTower.nil (X := X)).toBase := by
    rw [toBase_nil]
    infer_instance
  have := SmoothOfRelativeDimension.smooth 2 (X ↘ Spec (.of k))
  exact (ramificationIdealSheaf_congr k toBase_nil).trans
    (ramificationIdealSheaf_eq_top_of_isOpenImmersion k (𝟙 X))

private theorem ramificationIdealSheafToBase_snoc_point (hT : IsClosedPointTower X T)
    {I : Y.IdealSheafData}
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker) :
    (hT.snoc p hp hI).ramificationIdealSheafToBase k =
      I.comap I.blowupToBase * (hT.ramificationIdealSheafToBase k).comap I.blowupToBase := by
  have hcenter := hI.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal p)
  subst hcenter
  let I := vanishingIdeal (TopologicalSpace.Closeds.mk (closure (Set.singleton p)) isClosed_closure)
  let s := X ↘ Spec (.of k)
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ s⟩
  let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ (Y ↘ Spec (.of k))⟩
  have : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : I.blowupToBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension s
  have : SmoothOfRelativeDimension 2 (I.blowup ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowup_closed_point (Y ↘ Spec (.of k)) hp
  have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (I.blowup ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  rw [ramificationIdealSheafToBase_def, ramificationIdealSheafToBase_def]
  have hcomp := ramificationIdealSheaf_comp k I.blowupToBase T.toBase 2
  rw [ramificationIdealSheaf_blowup_of_smoothSurface k hp] at hcomp
  exact (ramificationIdealSheaf_congr k (toBase_snoc T I)).trans hcomp

/-- Adding a point blowup multiplies the total transform of the earlier ramification
ideal by the new exceptional ideal. -/
@[simp]
theorem ramificationIdealSheafToBase_snoc {I : Y.IdealSheafData}
    (h : IsClosedPointTower X (T.snoc I)) :
    h.ramificationIdealSheafToBase k =
      I.comap I.blowupToBase *
        ((snoc_iff.mp h).1.ramificationIdealSheafToBase k).comap I.blowupToBase := by
  obtain ⟨hT, p, hp, hI⟩ := snoc_iff.mp h
  exact ramificationIdealSheafToBase_snoc_point k hT p hp hI

/-- The support of the ramification ideal of a point-blowup tower is precisely
the inverse image of the locus where the projection is not an isomorphism. -/
theorem support_ramificationIdealSheafToBase (hT : IsClosedPointTower X T) :
    ((hT.ramificationIdealSheafToBase k).support : Set Y) =
      T.toBase ⁻¹' T.toBase.centre := by
  induction hT with
  | nil =>
    rw [toBase_nil, (Scheme.Hom.centre_eq_empty_iff (𝟙 X)).mpr inferInstance]
    simp
  | @snoc m W U I hU p hp hI ih =>
    let f := U.toBase ≫ X ↘ Spec (.of k)
    have : SmoothOfRelativeDimension 2 f := hU.smoothOfRelativeDimension _
    have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth f p
    have : IsRegular W := IsRegular.of_smooth f
    have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp
      inferInstance).2 p hp
    have hs := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    have hc : I.blowupToBase.centre = {p} :=
      hs ▸ centre_blowupToBase_closed_point hp hdim
    have : Surjective I.blowupToBase := hs ▸ surjective_blowupToBase_point hp hdim
    have : IsProper U.toBase := U.isProper_toBase
    have hsupport : (I.support : Set W) = {p} := by
      rw [hs, coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk, hp.closure_eq]
    rw [ramificationIdealSheafToBase_snoc, support_mul, TopologicalSpace.Closeds.coe_sup,
      support_comap, support_comap, TopologicalSpace.Closeds.coe_preimage,
      TopologicalSpace.Closeds.coe_preimage, hsupport, ih, toBase_snoc,
      Scheme.Hom.centre_comp, hc]
    ext x
    simp only [Set.mem_union, Set.mem_preimage, Scheme.Hom.comp_apply, Set.image_singleton,
      Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inr (congrArg U.toBase h)
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · by_cases hx : U.toBase (I.blowupToBase x) ∈ U.toBase.centre
        · exact Or.inr hx
        · apply Or.inl
          have h₁ : U.toBase (I.blowupToBase x) ∈ U.toBase.isoLocus := by
            simpa [Scheme.Hom.centre_def] using hx
          have h₂ : U.toBase p ∈ U.toBase.isoLocus := h ▸ h₁
          exact U.toBase.injOn_preimage_isoLocus h₁ h₂ h

/-- The ramification ideal of the projection of a point tower on a smooth integral
surface is effective Cartier. -/
theorem isEffectiveCartier_ramificationIdealSheafToBase [IsIntegral X] [IsNoetherian X]
    (hT : IsClosedPointTower X T) : (hT.ramificationIdealSheafToBase k).IsEffectiveCartier := by
  induction hT with
  | nil => simpa only [ramificationIdealSheafToBase_nil] using isEffectiveCartier_top X
  | @snoc m W S I hS p hp hI ih =>
    let s := X ↘ Spec (.of k)
    have : IsIntegral W := hS.isIntegral s
    have : IsNoetherian W := S.isNoetherian
    let : W.Over (Spec (.of k)) := ⟨S.toBase ≫ s⟩
    have : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) := hS.smoothOfRelativeDimension s
    let U := BlowupTower.nil.snoc I
    have hU : IsClosedPointTower W U := IsClosedPointTower.nil.snoc p hp hI
    rw [ramificationIdealSheafToBase_snoc k (hS.snoc p hp hI)]
    apply TauCeti.isEffectiveCartier_mul I.isEffectiveCartier_comap_blowupToBase
    simpa only [U, toBase_snoc, toBase_nil, Category.comp_id] using
      hU.isEffectiveCartier_totalTransform (W ↘ Spec (.of k)) ih

end QPainleve.BlowupTower.IsClosedPointTower
