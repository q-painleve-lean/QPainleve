/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.RepeatedCenter
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Exceptional configurations of disjoint internal blowups

For an ordered blowup tower at distinct closed points of a fixed boundary,
the scheme-theoretic inverse images of the original centers are pairwise disjoint
exceptional curves of the first kind. They have the prescribed total exceptional
classes and meet the strict boundary at the original centers as closed subschemes.

This is the exceptional configuration used in the proof of Theorem 1.8 of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i] {n : ℕ}
  (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier})

local notation "T" => Sigma.snd (alongBoundary i J)
local notation "E[" j "]" => Scheme.IdealSheafData.comap
  (Scheme.IdealSheafData.map (Subtype.val (J j)) i) (BlowupTower.toBase (WithBoundary.toTower (T)))

/-- The inverse images of two disjoint centers have disjoint supports in the final surface. -/
theorem pairwise_disjoint_support_comap_centers_alongBoundary
    (hd : Pairwise fun a b ↦ Disjoint ((J a).val.support : Set D) ((J b).val.support : Set D)) :
    Pairwise fun a b ↦ Disjoint (E[a].support : Set (alongBoundary i J).1)
      (E[b].support : Set (alongBoundary i J).1) := by
  intro a b hab
  simp only [support_comap, Closeds.coe_preimage, support_map_of_isClosedImmersion]
  exact (Set.disjoint_image_of_injective i.isClosedEmbedding.injective (hd hab)).preimage _

variable {k : Type u} [Field k]
variable (f : X ⟶ Spec (.of k))

private theorem exceptionalCurveOfFirstKind_snoc [SmoothOfRelativeDimension 2 f]
    {Y : Scheme.{u}} {m : ℕ} (P : WithBoundary i m Y)
    {p : D} (hp : IsClosed ({p} : Set D)) (hlocal : i p ∈ P.toTower.toBase.isoLocus) :
    let A := (D.fromSpecResidueField p).ker.map P.boundaryι
    (A.comap A.blowupToBase).IsExceptionalCurveOfFirstKind := by
  have hp' : IsClosed ({P.boundaryι p} : Set Y) := by
    simpa using P.boundaryι.isClosedEmbedding.isClosedMap _ hp
  have hp₀ : IsClosed ({i p} : Set X) := by
    simpa using i.isClosedEmbedding.isClosedMap _ hp
  have himage : P.toTower.toBase (P.boundaryι p) = i p := by
    rw [← Scheme.Hom.comp_apply, WithBoundary.boundaryι_toBase]
  have : IsIso (P.toTower.toBase.stalkMap (P.boundaryι p)) :=
    P.toTower.toBase.isIso_stalkMap_of_mem_isoLocus (himage.symm ▸ hlocal)
  let e := (asIso (P.toTower.toBase.stalkMap (P.boundaryι p))).commRingCatIsoToRingEquiv
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegularLocalRing (X.presheaf.stalk (P.toTower.toBase (P.boundaryι p))) :=
    himage.symm ▸ isRegularLocalRing_stalk_of_smooth f (i p)
  have : IsRegularLocalRing (Y.presheaf.stalk (P.boundaryι p)) := .of_ringEquiv e
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 _ hp₀
  dsimp only
  rw [P.boundaryι.map_ker_fromSpecResidueField]
  exact isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint _ hp'
    (e.ringKrullDim.symm.trans (himage.symm ▸ hdim))

private theorem exceptionalCurveOfFirstKind_class_snoc_castSucc {Y : Scheme.{u}} {m : ℕ}
    (P : BlowupTower X m Y) (A F : Y.IdealSheafData) (j : Fin m)
    (hF : F.IsExceptionalCurveOfFirstKind)
    (hclass : (LineBundleClass.mk hF.isEffectiveCartier.toInvertibleSheaf)⁻¹ = P.exceptionalClass j)
    (hd : Disjoint (F.support : Set Y) (A.support : Set Y)) :
    ∃ h : (F.comap A.blowupToBase).IsExceptionalCurveOfFirstKind,
      (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
        (P.snoc A).exceptionalClass j.castSucc := by
  let π := A.blowupToBase
  have hsub : (F.support : Set Y) ⊆ (A.support.compl : Set Y) :=
    fun _ hx ↦ Set.disjoint_left.mp hd hx
  have hlocal : (F.support : Set Y) ⊆ π.isoLocus :=
    hsub.trans (π.le_isoLocus_iff.mpr A.isIso_blowupToBase_restrict_compl_support)
  have := F.isIso_subschemeMap_blowupToBase_of_disjoint A hd
  let hE := hF.comap_of_isIso_subschemeMap π
    (hF.isEffectiveCartier.comap_of_support_subset_isoLocus π hlocal)
  refine ⟨hE, ?_⟩
  rw [exceptionalClass_snoc_castSucc, ← hclass, LineBundleClass.pullback_inv,
    hF.isEffectiveCartier.pullback_mk_toInvertibleSheaf hE.isEffectiveCartier]

include f in
/-- Blowing up disjoint reduced closed Cartier centers on a boundary of a smooth surface
realizes each marked total exceptional class by the exceptional curve over that center. -/
theorem exceptionalCurveOfFirstKind_alongBoundary [SmoothOfRelativeDimension 2 f]
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker)
    (hd : Pairwise fun a b ↦ Disjoint ((J a).val.support : Set D) ((J b).val.support : Set D))
    (j : Fin n) :
    ∃ h : E[j].IsExceptionalCurveOfFirstKind,
      (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
        (T).toTower.exceptionalClass j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    let C (a : Fin n) := J a.castSucc
    let U := alongBoundary i C
    let P := U.2
    let A := J (Fin.last n)
    have hC (a : Fin n) := hJ a.castSucc
    have hdC : Pairwise
        (fun a b ↦ Disjoint ((C a).val.support : Set D) ((C b).val.support : Set D)) :=
      hd.comp_of_injective (Fin.castSucc_injective _)
    have hlast (a : Fin n) : Disjoint ((C a).val.support : Set D) (A.val.support : Set D) :=
      hd (Fin.castSucc_ne_last a)
    have hlastMap (a : Fin n) :
        Disjoint (((C a).val.map i).support : Set X) ((A.val.map i).support : Set X) := by
      simpa only [support_map_of_isClosedImmersion,
        Set.disjoint_image_iff i.isClosedEmbedding.injective] using hlast a
    have hA : A.val.map P.boundaryι = (A.val.map i).comap P.toTower.toBase :=
      (comap_map_toBase_alongBoundary (i := i) C A.val hlast).symm
    rw [alongBoundary_succ, WithBoundary.toTower_snoc, toBase_snoc, comap_comp]
    refine Fin.lastCases ?_ (fun a ↦ ?_) j
    · rw [← hA]
      obtain ⟨p, hp, hpA⟩ := hJ (Fin.last n)
      let W : X.Opens := ⨅ a : Fin n, ((C a).val.map i).support.compl
      have hW (a : Fin n) : Disjoint (W : Set X) (((C a).val.map i).support : Set X) :=
        Set.disjoint_left.mpr fun _ hx ↦ (iInf_le (fun a ↦ ((C a).val.map i).support.compl) a) hx
      have hpA' : i p ∈ (A.val.map i).support := by
        rw [← SetLike.mem_coe, support_map_of_isClosedImmersion, hpA,
          Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
        exact Set.mem_image_of_mem _ (Set.mem_singleton _)
      have hWp : i p ∈ W := by
        simp only [W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter, Closeds.coe_compl,
          Set.mem_compl_iff]
        exact fun a ha ↦ Set.disjoint_left.mp (hlastMap a) ha hpA'
      have hlocal := P.toTower.toBase.le_isoLocus_iff.mpr
        (isIso_toBase_restrict_alongBoundary (i := i) C W hW) hWp
      have h := exceptionalCurveOfFirstKind_snoc i f P hp hlocal
      rw [← hpA] at h
      exact ⟨h, (exceptionalClass_snoc_last _ _).symm⟩
    · obtain ⟨hF, hclass⟩ := ih C hC hdC a
      let F := ((C a).val.map i).comap P.toTower.toBase
      have hsep : Disjoint (F.support : Set U.1) ((A.val.map P.boundaryι).support : Set U.1) := by
        simp only [F, hA, support_comap, Closeds.coe_preimage]
        exact (hlastMap a).preimage _
      exact exceptionalCurveOfFirstKind_class_snoc_castSucc _ _ _ a hF hclass hsep

section RootFree

variable (k) [IsAlgClosed k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- In the absence of internal curves of square `-2`, the total exceptional classes
of an internal point-blowup tower are represented by pairwise disjoint exceptional
curves of the first kind, each with its specified scheme-theoretic boundary intersection. -/
theorem exceptional_configuration_alongBoundary
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker)
    (hroot : let Y := (alongBoundary i J).1
      let : Y.Over (Spec (.of k)) := ⟨(T).toTower.toBase ≫ (X ↘ Spec (.of k))⟩
      ¬ ∃ (C : Scheme.{u}) (j : C ⟶ Y) (_ : IsClosedImmersion j) (_ : IsIntegral C)
          (hC : j.ker.IsEffectiveCartier),
        topologicalKrullDim C = 1 ∧ Disjoint (Set.range j) (Set.range (T).boundaryι) ∧
        Chow.classIntersectionNumber k Y (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹
          (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = -2) :
    Pairwise (fun a b ↦ Disjoint (E[a].support : Set (alongBoundary i J).1)
      (E[b].support : Set (alongBoundary i J).1)) ∧
    ∀ j : Fin n, ∃ h : E[j].IsExceptionalCurveOfFirstKind,
      (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
        (T).toTower.exceptionalClass j ∧ E[j].comap (T).boundaryι = (J j).val := by
  have hd : Pairwise
      (fun a b ↦ Disjoint ((J a).val.support : Set D) ((J b).val.support : Set D)) := by
    intro a b hab
    obtain ⟨p, hp, ha⟩ := hJ a
    obtain ⟨q, hq, hb⟩ := hJ b
    rw [ha, hb, Scheme.support_ker_fromSpecResidueField_of_isClosed hp,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hq, Set.disjoint_singleton]
    intro hpq
    subst q
    obtain ⟨C, hC, -, hint, hdim, hdis, hsq⟩ :=
      exists_internal_minus_two_curve_of_repeated_center (i := i) k J hJ hab (ha.trans hb.symm)
    let hι : C.subschemeι.ker.IsEffectiveCartier := C.ker_subschemeι.symm ▸ hC
    refine hroot ⟨C.subscheme, C.subschemeι, inferInstance, hint, hι, hdim, ?_, ?_⟩
    · simpa only [C.range_subschemeι] using hdis
    · rwa [LineBundleClass.mk_toInvertibleSheaf_congr hι hC C.ker_subschemeι]
  refine ⟨pairwise_disjoint_support_comap_centers_alongBoundary i J hd, fun j ↦ ?_⟩
  obtain ⟨h, hclass⟩ := exceptionalCurveOfFirstKind_alongBoundary i J (X ↘ Spec (.of k)) hJ hd j
  exact ⟨h, hclass, (T).comap_map_toBase_boundaryι (J j).val⟩

end RootFree

end QPainleve.BlowupTower
