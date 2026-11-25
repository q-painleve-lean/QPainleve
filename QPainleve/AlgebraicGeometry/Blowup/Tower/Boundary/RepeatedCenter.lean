/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

import Mathlib.Algebra.BigOperators.Fin
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Intersection
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Residual
import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Stalk
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Repeated centers on the boundary of a surface

The exceptional curve created at a smooth boundary point meets the new boundary
in that point. A second blowup there separates the two curves and changes the
self-intersection of the old exceptional curve from `-1` to `-2`. All later
blowups along the boundary leave this strict transform unchanged.

This is the obstruction to repeated internal centers in the root-free case of
Gross, Hacking and Keel, [*Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 4.7](https://arxiv.org/html/1211.6367v5#S4.Thmtheorem7).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D X Y : Scheme.{u}} {i : D ⟶ X} {n : ℕ}

private theorem WithBoundary.isClosed_boundary_point (T : WithBoundary i n Y)
    {p : D} (hp : IsClosed ({p} : Set D)) :
    IsClosed ({T.boundaryι p} : Set Y) := by
  simpa using T.boundaryι.isClosedEmbedding.isClosedMap _ hp

variable (k : Type u) [Field k] [IsAlgClosed k]

private theorem WithBoundary.exists_exceptional_at (T : WithBoundary i n Y)
    [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    {p : D} (hp : IsClosed ({p} : Set D))
    (hpC : (D.fromSpecResidueField p).ker.IsEffectiveCartier) :
    let J := (D.fromSpecResidueField p).ker
    let I := J.map T.boundaryι
    let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ (Y ↘ Spec (.of k))⟩
    ∃ (C : I.blowup.IdealSheafData) (hC : C.IsEffectiveCartier),
      IsRegular C.subscheme ∧ IsIntegral C.subscheme ∧ topologicalKrullDim C.subscheme = 1 ∧
      C.comap (T.snoc J hpC).boundaryι = J ∧
      Chow.classIntersectionNumber k I.blowup (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = -1 := by
  let J := (D.fromSpecResidueField p).ker
  let I := J.map T.boundaryι
  let C := I.comap I.blowupToBase
  let f := Y ↘ Spec (.of k)
  let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ f⟩
  have hp' := T.isClosed_boundary_point hp
  have hI := T.boundaryι.map_ker_fromSpecResidueField p
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular Y := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 _ hp'
  have hE : C.IsExceptionalCurveOfFirstKind := by
    exact (congrArg (fun K : Y.IdealSheafData ↦
      (K.comap K.blowupToBase).IsExceptionalCurveOfFirstKind) hI).mpr
      (isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint _ hp' hd)
  have hInt := hE.isIntegral_subscheme
  have hDim := hE.topologicalKrullDim_subscheme
  obtain ⟨_, F, _, e, -⟩ := hE
  have : Smooth (projectiveLine F ↘ Spec (.of F)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular (projectiveLine F) := IsRegular.of_smooth (projectiveLine F ↘ Spec (.of F))
  let hC := I.isEffectiveCartier_comap_blowupToBase
  refine ⟨C, hC, IsRegular.of_isOpenImmersion e.inv, hInt, hDim,
    T.comap_exceptional_boundaryι_snoc J hpC, ?_⟩
  let P (K : Y.IdealSheafData) : Prop :=
    let : K.blowup.Over (Spec (.of k)) := ⟨K.blowupToBase ≫ f⟩
    Chow.classIntersectionNumber k K.blowup K.blowupExceptionalClass K.blowupExceptionalClass = -1
  rw [← blowupExceptionalClass_def]
  refine (congrArg P hI).mpr ?_
  let K := (Y.fromSpecResidueField (T.boundaryι p)).ker
  let : K.blowup.Over (Spec (.of k)) := ⟨K.blowupToBase ≫ f⟩
  have hproj : K.blowup.IsProjectiveOver k := K.isProjectiveOver_blowup_of_isNoetherianRing k
  simpa [P, blowupExceptionalClass_def, Chow.classIntersectionNumber_one_left] using
    Chow.classIntersectionNumber_pointBlowup (T.boundaryι p) k hp' 1 1 1 1 hproj

private theorem WithBoundary.strictTransform_curve (T : WithBoundary i n Y)
    [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    {p : D} (hp : IsClosed ({p} : Set D)) (hpC : (D.fromSpecResidueField p).ker.IsEffectiveCartier)
    {C : Y.IdealSheafData} (hC : C.IsEffectiveCartier)
    [IsRegular C.subscheme] [IsIntegral C.subscheme] (hdim : topologicalKrullDim C.subscheme = 1) :
    let J := (D.fromSpecResidueField p).ker
    let I := J.map T.boundaryι
    let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ (Y ↘ Spec (.of k))⟩
    ∃ (C' : I.blowup.IdealSheafData) (hC' : C'.IsEffectiveCartier),
      IsRegular C'.subscheme ∧ IsIntegral C'.subscheme ∧
      topologicalKrullDim C'.subscheme = 1 ∧
      C'.comap (T.snoc J hpC).boundaryι * J ^ (C.stalkOrder (T.boundaryι p)).toNat =
        C.comap T.boundaryι ∧
      Chow.classIntersectionNumber k I.blowup (LineBundleClass.mk hC'.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hC'.toInvertibleSheaf)⁻¹ =
        Chow.classIntersectionNumber k Y (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹
          (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ -
          ((C.stalkOrder (T.boundaryι p)).toNat : ℤ) ^ 2 := by
  let J := (D.fromSpecResidueField p).ker
  let I := J.map T.boundaryι
  let f := Y ↘ Spec (.of k)
  let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ f⟩
  have hp' := T.isClosed_boundary_point hp
  have hI : I = (Y.fromSpecResidueField (T.boundaryι p)).ker :=
    T.boundaryι.map_ker_fromSpecResidueField p
  -- On the regular curve the inverse image of the center is empty or a reduced closed point.
  have hcart : (I.comap C.subschemeι).IsEffectiveCartier := by
    rw [hI]
    by_cases h : T.boundaryι p ∈ Set.range C.subschemeι
    · obtain ⟨q, hq⟩ := h
      have hclosed : IsClosed ({q} : Set C.subscheme) := by
        have he : C.subschemeι ⁻¹' {T.boundaryι p} = {q} := by
          rw [← hq, ← Set.image_singleton]
          exact C.subschemeι.isClosedEmbedding.injective.preimage_image _
        exact he ▸ hp'.preimage C.subschemeι.continuous
      rw [← hq, C.subschemeι.comap_ker_fromSpecResidueField_apply]
      exact C.subscheme.isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hclosed hdim
    · have htop : ((Y.fromSpecResidueField (T.boundaryι p)).ker.comap C.subschemeι) = ⊤ := by
        rw [comap_eq_top_iff, ← Opens.coe_eq_univ]
        simpa [Closeds.compl, Scheme.support_ker_fromSpecResidueField_of_isClosed hp',
          Set.preimage_eq_empty_iff] using h
      rw [htop]
      exact isEffectiveCartier_top _
  let j := I.blowupLift C.subschemeι hcart
  have : IsClosedImmersion j := I.isClosedImmersion_blowupLift _ _
  have hker : j.ker = (I.blowupMap C.subschemeι).ker := by
    rw [ker_blowupLift, ker_blowupMap]
  have hsq := Chow.classIntersectionNumber_self_strictTransform_pointBlowup (T.boundaryι p) k hp' hC
  dsimp only at hsq
  rw [← hI, ← hker] at hsq
  obtain ⟨hC', hsq⟩ := hsq
  refine ⟨j.ker, hC', IsRegular.of_isOpenImmersion (inv j.toImage),
    IsIntegral.of_isIso j.toImage,
    j.toImage.homeomorph.isHomeomorph.topologicalKrullDim_eq.symm.trans hdim, ?_, hsq⟩
  have : IsNoetherian Y := isNoetherian_of_finiteType f
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular Y := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 _ hp'
  have he := hC.totalTransform_eq_strictTransform_mul_pow_closedPoint hp' hd
  rw [← Y.ker_fromSpecResidueField_eq_vanishingIdeal, ← hI] at he
  dsimp only at he
  rw [← hker] at he
  have hre := congrArg (fun F ↦ F.comap (T.snoc J hpC).boundaryι) he.symm
  simp only [comap_mul, comap_pow] at hre
  rw [T.comap_exceptional_boundaryι_snoc J hpC, ← comap_comp,
    T.boundaryι_snoc_blowupToBase] at hre
  exact hre

private def HasBoundaryCurve [Y.Over (Spec (.of k))] (b : D ⟶ Y) (J : D.IdealSheafData)
    (a : ℤ) : Prop :=
  ∃ (C : Y.IdealSheafData) (hC : C.IsEffectiveCartier),
    IsRegular C.subscheme ∧ IsIntegral C.subscheme ∧ topologicalKrullDim C.subscheme = 1 ∧
    C.comap b = J ∧ Chow.classIntersectionNumber k Y
      (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = a

open Classical in
private theorem WithBoundary.stalkOrder_at_center (T : WithBoundary i n Y) [IsRegular Y]
    {C : Y.IdealSheafData} (hC : C.IsEffectiveCartier) [IsRegular C.subscheme] (q : D) :
    C.stalkOrder (T.boundaryι q) =
      if q ∈ ((C.comap T.boundaryι).support : Set D) then 1 else 0 := by
  classical
  rw [support_comap, Closeds.coe_preimage, Set.mem_preimage]
  split_ifs with h
  · obtain ⟨x, hx⟩ := C.range_subschemeι.symm ▸ h
    rw [← hx]
    exact (hC.stalkOrder_eq_one_iff_isRegularLocalRing x).2 inferInstance
  · exact (C.stalkOrder_eq_zero_iff _).mpr h

open Classical in
private theorem WithBoundary.hasBoundaryCurve_snoc (T : WithBoundary i n Y)
    [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
    [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
    {p q : D} (hp : IsClosed ({p} : Set D)) (hq : IsClosed ({q} : Set D))
    (hqC : (D.fromSpecResidueField q).ker.IsEffectiveCartier) (m : ℕ) (hmpos : 0 < m)
    (h : HasBoundaryCurve k T.boundaryι
      (if m = 1 then (D.fromSpecResidueField p).ker else ⊤) (if m = 1 then -1 else -2)) :
    let J := (D.fromSpecResidueField q).ker
    let I := J.map T.boundaryι
    let m' := m + if q = p then 1 else 0
    let : I.blowup.Over (Spec (.of k)) := ⟨I.blowupToBase ≫ (Y ↘ Spec (.of k))⟩
    HasBoundaryCurve k (T.snoc J hqC).boundaryι
      (if m' = 1 then (D.fromSpecResidueField p).ker else ⊤) (if m' = 1 then -1 else -2) := by
  classical
  intro J I m'
  obtain ⟨C, hC, hreg, hint, hdim, hrest, hsq⟩ := h
  obtain ⟨C', hC', hreg', hint', hdim', hrest', hsq'⟩ :=
    T.strictTransform_curve k hq hqC hC hdim
  refine ⟨C', hC', hreg', hint', hdim', ?_⟩
  have : Smooth (Y ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegular Y := IsRegular.of_smooth (Y ↘ Spec (.of k))
  have hord := T.stalkOrder_at_center hC q
  rw [hrest] at hord
  by_cases hm : m = 1
  · subst m
    by_cases hpq : q = p
    · subst q
      have hone : C.stalkOrder (T.boundaryι p) = 1 := by
        simpa [Scheme.support_ker_fromSpecResidueField_of_isClosed hp] using hord
      -- The new exceptional divisor accounts for the entire intersection with the boundary.
      have hr : C'.comap (T.snoc J hqC).boundaryι = ⊤ := by
        apply hqC.mul_left_cancel
        simpa [hone, hrest, mul_comm, J] using hrest'
      rw [hsq, hone] at hsq'
      exact ⟨by simpa [m'] using hr, by simpa [m'] using hsq'⟩
    · have hzero : C.stalkOrder (T.boundaryι q) = 0 := by
        simpa [hpq, Scheme.support_ker_fromSpecResidueField_of_isClosed hp] using hord
      rw [hsq, hzero] at hsq'
      exact ⟨by simpa [m', hpq, hzero, hrest] using hrest',
        by simpa [m', hpq] using hsq'⟩
  · have hm' : m' ≠ 1 := by
      dsimp only [m']
      split_ifs <;> omega
    have hzero : C.stalkOrder (T.boundaryι q) = 0 := by simpa [hm] using hord
    rw [hsq, hzero] at hsq'
    exact ⟨by simpa [hm', hm, hzero, hrest] using hrest',
      by simpa [hm', hm] using hsq'⟩

private noncomputable def centerCount (p : D) {n : ℕ}
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}) : ℕ := by
  classical
  exact (Finset.univ.filter fun j ↦ (J j).val = (D.fromSpecResidueField p).ker).card

open Classical in
private theorem centerCount_succ (p : D) {n : ℕ}
    (J : Fin (n + 1) → {I : D.IdealSheafData // I.IsEffectiveCartier}) :
    centerCount p J = centerCount p (J ∘ Fin.castSucc) +
      if (J (Fin.last n)).val = (D.fromSpecResidueField p).ker then 1 else 0 := by
  classical
  simp only [centerCount, Finset.card_filter, Fin.sum_univ_castSucc, Function.comp_apply]

variable [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] [IsClosedImmersion i]

private theorem hasBoundaryCurve_alongBoundary
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker)
    {p : D} (hp : IsClosed ({p} : Set D)) (hm : 0 < centerCount p J) :
    let M := alongBoundary i J
    let : M.1.Over (Spec (.of k)) := ⟨M.2.toTower.toBase ≫ (X ↘ Spec (.of k))⟩
    HasBoundaryCurve k M.2.boundaryι
      (if centerCount p J = 1 then (D.fromSpecResidueField p).ker else ⊤)
      (if centerCount p J = 1 then -1 else -2) := by
  classical
  induction n with
  | zero => simp [centerCount] at hm
  | succ n ih =>
    let J₀ := J ∘ Fin.castSucc
    let T := (alongBoundary i J₀).2
    let f := X ↘ Spec (.of k)
    let g := T.toTower.toBase ≫ f
    rw [centerCount_succ] at hm ⊢
    obtain ⟨q, hq, hqJ⟩ := hJ (Fin.last n)
    let hqC := hqJ ▸ (J (Fin.last n)).property
    have hlast : J (Fin.last n) = ⟨(D.fromSpecResidueField q).ker, hqC⟩ := Subtype.ext hqJ
    let target (M : Σ W, WithBoundary i (n + 1) W) : Prop :=
      let m := centerCount p J₀ + if q = p then 1 else 0
      let : M.1.Over (Spec (.of k)) := ⟨M.2.toTower.toBase ≫ f⟩
      HasBoundaryCurve k M.2.boundaryι
        (if m = 1 then (D.fromSpecResidueField p).ker else ⊤) (if m = 1 then -1 else -2)
    rw [hqJ, Scheme.ker_fromSpecResidueField_inj] at hm ⊢
    let extend (L : {I : D.IdealSheafData // I.IsEffectiveCartier}) :
        Σ W, WithBoundary i (n + 1) W := ⟨_, T.snoc L.val L.property⟩
    have hstep := (alongBoundary_succ i J).trans (congrArg extend hlast)
    refine (congrArg target hstep).mpr ?_
    dsimp only [target, extend, Sigma.snd]
    rw [WithBoundary.toTower_snoc, toBase_snoc, Category.assoc]
    let : (alongBoundary i J₀).1.Over (Spec (.of k)) := ⟨g⟩
    have hTower := isClosedPointTower_alongBoundary i J₀ (fun j ↦ hJ j.castSucc)
    have : IsNoetherian X := isNoetherian_of_finiteType f
    have : IsIntegral (alongBoundary i J₀).1 := hTower.isIntegral f
    have : (alongBoundary i J₀).1.IsProjectiveOver k := T.toTower.isProjectiveOver k
    have : SmoothOfRelativeDimension 2 ((alongBoundary i J₀).1 ↘ Spec (.of k)) :=
      hTower.smoothOfRelativeDimension f
    by_cases hm₀ : centerCount p J₀ = 0
    · have hqp : q = p := by
        by_contra he
        apply hm₀.not_gt
        simpa only [he, ite_false, add_zero] using hm
      subst q
      simpa only [HasBoundaryCurve, hm₀, ite_true, zero_add] using! T.exists_exceptional_at k hp hqC
    · have hmpos := Nat.pos_of_ne_zero hm₀
      exact T.hasBoundaryCurve_snoc k hp hq hqC _ hmpos
        (ih J₀ (fun j ↦ hJ j.castSucc) hmpos)

/-- A repeated reduced point among the Cartier centers on a fixed boundary produces a
regular integral curve of self-intersection `-2` disjoint from the final boundary.
The two occurrences can be separated by any number of other blowups, and the
curve persists through all later centers. -/
theorem exists_internal_minus_two_curve_of_repeated_center
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker)
    {a b : Fin n} (hab : a ≠ b) (heq : (J a).val = (J b).val) :
    let M := alongBoundary i J
    let : M.1.Over (Spec (.of k)) := ⟨M.2.toTower.toBase ≫ (X ↘ Spec (.of k))⟩
    ∃ (C : M.1.IdealSheafData) (hC : C.IsEffectiveCartier),
      IsRegular C.subscheme ∧ IsIntegral C.subscheme ∧ topologicalKrullDim C.subscheme = 1 ∧
      Disjoint (C.support : Set M.1) (Set.range M.2.boundaryι) ∧
      Chow.classIntersectionNumber k M.1 (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = -2 := by
  classical
  obtain ⟨p, hp, ha⟩ := hJ a
  have hm : 1 < centerCount p J :=
    Finset.one_lt_card.mpr ⟨a, by simp [ha], b, by simp [← heq, ha], hab⟩
  have h := hasBoundaryCurve_alongBoundary (i := i) k J hJ hp (zero_lt_one.trans hm)
  simp only [ite_eq_right hm.ne'] at h
  obtain ⟨C, hC, hreg, hint, hdim, hrest, hsq⟩ := h
  refine ⟨C, hC, hreg, hint, hdim, Set.disjoint_left.mpr ?_, hsq⟩
  rintro _ hCmem ⟨y, rfl⟩
  have hy : y ∈ ((C.comap (alongBoundary i J).2.boundaryι).support : Set D) := by
    simpa only [support_comap, Closeds.coe_preimage, Set.mem_preimage] using hCmem
  simp [hrest] at hy

end QPainleve.BlowupTower
