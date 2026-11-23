/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Strict transforms in the Picard marking of a point blowup tower

At each blowup, take the scheme-theoretic strict transform of the previous divisor.
Its exceptional coordinate in the ordered Picard marking is minus its order at the
current center. The coordinates refer to total exceptional classes, so the formula
also applies to infinitely near centers.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData.IsEffectiveCartier (toInvertibleSheaf)

universe u

namespace QPainleve.BlowupTower

variable {X Y : Scheme.{u}} {n : ℕ}

/-- The iterated scheme-theoretic strict transform of an ideal sheaf, using the
specified centers in tower order. -/
def strictTransform (D : X.IdealSheafData) :
    {n : ℕ} → {Y : Scheme.{u}} → BlowupTower X n Y → Y.IdealSheafData
  | _, _, .nil => D
  | _, _, .snoc T I => (I.blowupMap (T.strictTransform D).subschemeι).ker

@[simp]
theorem strictTransform_nil (D : X.IdealSheafData) :
    (nil (X := X)).strictTransform D = D := (rfl)

@[simp]
theorem strictTransform_snoc (T : BlowupTower X n Y) (I : Y.IdealSheafData)
    (D : X.IdealSheafData) :
    (T.snoc I).strictTransform D = (I.blowupMap (T.strictTransform D).subschemeι).ker := (rfl)

namespace IsClosedPointTower

variable {T : BlowupTower X n Y}

private def lastCenter {I : Y.IdealSheafData} (hT : IsClosedPointTower X (T.snoc I)) :
    {p : Y // IsClosed ({p} : Set Y) ∧ I = (Y.fromSpecResidueField p).ker} :=
  ⟨(snoc_iff.mp hT).2.choose, (snoc_iff.mp hT).2.choose_spec⟩

private theorem lastCenter_eq {I : Y.IdealSheafData} (hT : IsClosedPointTower X (T.snoc I))
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker) :
    (lastCenter hT).val = p := by
  let q := lastCenter hT
  have h := congrArg (fun J : Y.IdealSheafData ↦ (J.support : Set Y))
    (q.property.2.symm.trans hI)
  simpa [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, q.property.1.closure_eq,
    hp.closure_eq] using h

/-- The exceptional coefficients of the iterated strict transform. At stage `j` the
coefficient is minus the natural-number value of the stalk order of the previous strict
transform at the current center. For an effective Cartier divisor on an integral smooth
surface these orders are finite. -/
def strictTransformCoefficients (D : X.IdealSheafData) :
    {n : ℕ} → {Y : Scheme.{u}} → {T : BlowupTower X n Y} →
      IsClosedPointTower X T → Fin n → ℤ
  | _, _, .nil, _ => 0
  | _, _, .snoc T I, h =>
    Fin.lastCases (-(ENat.toNat ((T.strictTransform D).stalkOrder (lastCenter h).val) : ℤ))
      (strictTransformCoefficients D (snoc_iff.mp h).1)

@[simp]
theorem strictTransformCoefficients_snoc_castSucc (D : X.IdealSheafData)
    {I : Y.IdealSheafData} (h : IsClosedPointTower X (T.snoc I)) (j : Fin n) :
    h.strictTransformCoefficients D j.castSucc =
      (snoc_iff.mp h).1.strictTransformCoefficients D j := by
  simp only [strictTransformCoefficients, Fin.lastCases_castSucc]

/-- The last coordinate is computed on the scheme immediately before the last blowup. -/
theorem strictTransformCoefficients_snoc_last (D : X.IdealSheafData)
    {I : Y.IdealSheafData} (h : IsClosedPointTower X (T.snoc I))
    (p : Y) (hp : IsClosed ({p} : Set Y)) (hI : I = (Y.fromSpecResidueField p).ker) :
    h.strictTransformCoefficients D (Fin.last n) =
      -(ENat.toNat ((T.strictTransform D).stalkOrder p) : ℤ) := by
  simp only [strictTransformCoefficients, Fin.lastCases_last, lastCenter_eq h p hp hI]

variable {k : Type u} [Field k] [PerfectField k] [hX : IsIntegral X] [hNX : IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [hf : SmoothOfRelativeDimension 2 f]
  {D : X.IdealSheafData}

include hX hNX hf in
/-- The iterated strict transform of a Cartier divisor in a point blowup tower on
a smooth integral surface is effective Cartier. -/
theorem isEffectiveCartier_strictTransform (hT : IsClosedPointTower X T)
    (hD : D.IsEffectiveCartier) : (T.strictTransform D).IsEffectiveCartier := by
  induction hT with
  | nil => simpa using hD
  | @snoc d W S I hS p hp hI ih =>
    let g := S.toBase ≫ f
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    rw [strictTransform_snoc, hI, W.ker_fromSpecResidueField_eq_vanishingIdeal]
    exact ih.strictTransform_pointBlowup hp hdim

local notation "classOf" h =>
  Additive.ofMul (LineBundleClass.mk (toInvertibleSheaf h))⁻¹

/-- The ordered Picard marking of a strict transform has the original divisor as its base
coordinate and the negative orders of the successive transforms as its exceptional coordinates. -/
theorem picardMarking_strictTransform (hT : IsClosedPointTower X T) (hD : D.IsEffectiveCartier) :
    T.picardMarking hT f (classOf hD, hT.strictTransformCoefficients D) =
      classOf (hT.isEffectiveCartier_strictTransform f hD) := by
  induction hT with
  | nil => simp
  | @snoc d W S I hS p hp hI ih =>
    let g := S.toBase ≫ f
    have : IsIntegral W := hS.isIntegral f
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegularLocalRing (W.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth g p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have hprev := hS.isEffectiveCartier_strictTransform f hD
    have hcalc := hprev.toLineBundleClass_strictTransform_pointBlowup hp hdim
    have hbase : I = Scheme.IdealSheafData.vanishingIdeal
        ⟨closure {p}, isClosed_closure⟩ := hI.trans (W.ker_fromSpecResidueField_eq_vanishingIdeal p)
    apply Additive.toMul.injective
    rw [picardMarking_apply, picardHom_snoc_apply_toMul]
    simp only [strictTransformCoefficients_snoc_castSucc]
    rw [← picardMarking_apply S hS f, ih,
      strictTransformCoefficients_snoc_last D (hS.snoc p hp hI) p hp hI,
      zpow_neg, zpow_natCast, ← inv_pow]
    cases hbase
    exact hcalc.symm

end IsClosedPointTower

section AlongBoundary

variable {C D : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
  (e : C ⟶ D) [IsClosedImmersion e]

private theorem ker_blowupLift_comp {I : X.IdealSheafData} (j : D ⟶ X) [IsClosedImmersion j]
    (h : (I.comap j).IsEffectiveCartier) (he : (I.comap (e ≫ j)).IsEffectiveCartier) :
    (I.blowupMap (e ≫ j).ker.subschemeι).ker = (e ≫ I.blowupLift j h).ker := by
  let g := e ≫ j
  have hcomp : g.toImage ≫ g.ker.subschemeι = g := by simp
  have hCartier : (I.comap g.ker.subschemeι).IsEffectiveCartier := by
    have hG : (I.comap g).IsEffectiveCartier := he
    have he' := hG.comap (inv g.toImage)
    have hInv : inv g.toImage ≫ g = g.ker.subschemeι := by
      calc
        _ = inv g.toImage ≫ (g.toImage ≫ g.ker.subschemeι) :=
          congrArg (inv g.toImage ≫ ·) hcomp.symm
        _ = _ := IsIso.inv_hom_id_assoc _ _
    simpa only [← Scheme.IdealSheafData.comap_comp, hInv] using he'
  have hLift : g.toImage ≫ I.blowupLift g.ker.subschemeι hCartier = e ≫ I.blowupLift j h := by
    apply I.blowup_hom_ext
    · simpa only [Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase] using hcomp
    · simpa only [Category.assoc, Scheme.IdealSheafData.blowupLift_blowupToBase, hcomp] using he
  have : IsIso (I.comap g.ker.subschemeι).blowupToBase :=
    (Scheme.IdealSheafData.isIso_blowupToBase_iff _).mpr hCartier
  rw [← hLift, ← I.blowupToBase_comp_blowupLift g.ker.subschemeι hCartier,
    Scheme.Hom.ker_comp_of_isIso]
  exact (Scheme.Hom.ker_comp_of_isIso g.toImage _).symm

/-- A closed subscheme of the fixed boundary stays embedded in the ordered blowups as its
iterated strict transform when each prescribed center pulls back to a Cartier ideal on it. -/
theorem strictTransform_ker_comp_alongBoundary
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (he : ∀ a, ((J a).val.comap e).IsEffectiveCartier) :
    (alongBoundary i J).2.toTower.strictTransform (e ≫ i).ker =
      (e ≫ (alongBoundary i J).2.boundaryι).ker := by
  let P {m : ℕ} (S : Σ W, WithBoundary i m W) :=
    S.2.toTower.strictTransform (e ≫ i).ker = (e ≫ S.2.boundaryι).ker
  induction n with
  | zero =>
    refine (congrArg P (alongBoundary_zero i J)).mpr ?_
    simp only [P, WithBoundary.toTower_nil, strictTransform_nil, WithBoundary.boundaryι_nil]
  | succ d ih =>
    refine (congrArg P (alongBoundary_succ i J)).mpr ?_
    let T := (alongBoundary i (fun j : Fin d ↦ J j.castSucc)).2
    let K := (J (Fin.last d)).val
    have h := ih (fun j ↦ J j.castSucc) (fun j ↦ he j.castSucc)
    have hcomp : ((K.map T.boundaryι).comap (e ≫ T.boundaryι)).IsEffectiveCartier := by
      rw [Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
      exact he (Fin.last d)
    have hK : ((K.map T.boundaryι).comap T.boundaryι).IsEffectiveCartier := by
      simpa only [Scheme.IdealSheafData.comap_map_of_isClosedImmersion] using
        (J (Fin.last d)).property
    -- Name the prefix and its center to keep the dependent blowup type fixed.
    change (T.snoc K (J (Fin.last d)).property).toTower.strictTransform (e ≫ i).ker =
      (e ≫ (T.snoc K (J (Fin.last d)).property).boundaryι).ker
    simp only [WithBoundary.toTower_snoc, strictTransform_snoc, WithBoundary.boundaryι_snoc]
    rw [h]
    exact ker_blowupLift_comp e T.boundaryι hK hcomp

omit [IsClosedImmersion i] in
private theorem stalkOrder_prefix_ker {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {T : WithBoundary i n Y} (hT : IsClosedPointTower X T.toTower)
    (hC : (e ≫ T.boundaryι).ker.IsEffectiveCartier) (p : D)
    (hreg : ∀ q : C, e q = p → IsRegularLocalRing (C.presheaf.stalk q))
    [Decidable (p ∈ Set.range e)] :
    (e ≫ T.boundaryι).ker.stalkOrder (T.boundaryι p) = if p ∈ Set.range e then 1 else 0 := by
  let g := e ≫ T.boundaryι
  have hrange : (g.ker.support : Set Y) = Set.range g := by
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq]
  by_cases hp : p ∈ Set.range e
  · rw [ite_eq_left hp]
    obtain ⟨q, hq⟩ := hp
    let a := g.toImage q
    have ha : g.ker.subschemeι a = T.boundaryι p := by
      rw [← Scheme.Hom.comp_apply g.toImage g.ker.subschemeι, Scheme.Hom.toImage_imageι]
      exact congrArg T.boundaryι hq
    have := hT.smoothOfRelativeDimension f
    have : Smooth (T.toTower.toBase ≫ f) := SmoothOfRelativeDimension.smooth 2 _
    have : IsRegularLocalRing (Y.presheaf.stalk (g.ker.subschemeι a)) :=
      isRegularLocalRing_stalk_of_smooth (T.toTower.toBase ≫ f) _
    have hOrder := (hC.stalkOrder_eq_one_iff_isRegularLocalRing a).mpr
      ((isRegularLocalRing_stalk_iff_of_isOpenImmersion g.toImage q).mpr (hreg q hq))
    exact ha ▸ hOrder
  · rw [ite_eq_right hp, Scheme.IdealSheafData.stalkOrder_eq_zero_iff]
    intro hm
    have hm' : T.boundaryι p ∈ (g.ker.support : Set Y) := hm
    rw [hrange] at hm'
    obtain ⟨q, hq⟩ := hm'
    exact hp ⟨q, T.boundaryι.isClosedEmbedding.injective hq⟩

variable {k : Type u} [Field k] [PerfectField k] [hX : IsIntegral X] [hNX : IsNoetherian X]
  (f : X ⟶ Spec (.of k)) [hf : SmoothOfRelativeDimension 2 f]

include hX hNX hf in
/-- In an ordered blowup tower along a fixed boundary, a component regular at the
centers on it has exceptional coordinate `-1` exactly at the centers on that component.
This uses membership on the original boundary, even for repeated centers. -/
theorem strictTransformCoefficients_alongBoundary
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (p : Fin n → D) (hp : ∀ a, IsClosed ({p a} : Set D))
    (hJ : ∀ a, (J a).val = (D.fromSpecResidueField (p a)).ker)
    (he : ∀ a, ((J a).val.comap e).IsEffectiveCartier)
    (hreg : ∀ a q, e q = p a → IsRegularLocalRing (C.presheaf.stalk q))
    (hC : (e ≫ i).ker.IsEffectiveCartier)
    (hT : IsClosedPointTower X (alongBoundary i J).2.toTower)
    [∀ a, Decidable (p a ∈ Set.range e)] :
    hT.strictTransformCoefficients (e ≫ i).ker =
      fun a ↦ if p a ∈ Set.range e then -1 else 0 := by
  let P {m : ℕ} (b : Fin m → ℤ) (U : Σ W, WithBoundary i m W) :=
    ∀ h : IsClosedPointTower X U.2.toTower, h.strictTransformCoefficients (e ≫ i).ker = b
  induction n with
  | zero => exact funext fun a ↦ a.elim0
  | succ d ih =>
    refine (congrArg (P fun a ↦ if p a ∈ Set.range e then -1 else 0)
      (alongBoundary_succ i J)).mpr ?_ hT
    let T := (alongBoundary i (fun a : Fin d ↦ J a.castSucc)).2
    let K := (J (Fin.last d)).val
    let b (a : Fin (d + 1)) : ℤ := if p a ∈ Set.range e then -1 else 0
    let goal (S : BlowupTower X (d + 1) (K.map T.boundaryι).blowup) :=
      ∀ h : IsClosedPointTower X S, h.strictTransformCoefficients (e ≫ i).ker = b
    refine (congrArg goal (WithBoundary.toTower_snoc T K (J (Fin.last d)).property)).mpr ?_
    intro hTower
    have hPrev := (IsClosedPointTower.snoc_iff.mp hTower).1
    have hStrict := strictTransform_ker_comp_alongBoundary i e (fun a : Fin d ↦ J a.castSucc)
      (fun a ↦ he a.castSucc)
    have hCPrefix : (e ≫ T.boundaryι).ker.IsEffectiveCartier :=
      hStrict ▸ hPrev.isEffectiveCartier_strictTransform f hC
    funext a
    refine Fin.lastCases ?_ (fun j ↦ ?_) a
    · have hclosed : IsClosed ({T.boundaryι (p (Fin.last d))} : Set _) := by
        simpa using T.boundaryι.isClosedEmbedding.isClosedMap _ (hp (Fin.last d))
      have hK : K = (D.fromSpecResidueField (p (Fin.last d))).ker := hJ (Fin.last d)
      have hmap : K.map T.boundaryι =
          (Scheme.fromSpecResidueField _ (T.boundaryι (p (Fin.last d)))).ker := by
        rw [hK, Scheme.IdealSheafData.map_ker,
          ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Scheme.Hom.ker_comp_of_isIso]
      rw [hTower.strictTransformCoefficients_snoc_last _ _ hclosed hmap, hStrict,
        stalkOrder_prefix_ker i e f hPrev hCPrefix _ (hreg (Fin.last d))]
      by_cases ha : p (Fin.last d) ∈ Set.range e <;> simp [b, ha]
    · rw [IsClosedPointTower.strictTransformCoefficients_snoc_castSucc]
      exact congrFun (ih _ _ (fun a ↦ hp a.castSucc) (fun a ↦ hJ a.castSucc)
        (fun a ↦ he a.castSucc) (fun a ↦ hreg a.castSucc) hPrev) j

end AlongBoundary

end QPainleve.BlowupTower
