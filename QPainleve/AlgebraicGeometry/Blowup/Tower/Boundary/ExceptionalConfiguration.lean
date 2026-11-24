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
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

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
      have hpA' : i p ∈ (A.val.map i).support := by
        rw [← SetLike.mem_coe, support_map_of_isClosedImmersion, hpA,
          Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
        exact Set.mem_image_of_mem _ (Set.mem_singleton _)
      have hlocal : i p ∈ P.toTower.toBase.isoLocus :=
        mem_isoLocus_toBase_alongBoundary i C fun a ↦ by
          simpa only [support_map_of_isClosedImmersion] using
            Set.disjoint_right.mp (hlastMap a) hpA'
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

/-- An exceptional curve over a reduced closed boundary center is internal.
The projection is injective on the strict boundary and constant on this curve. -/
theorem exceptional_support_not_le_boundary_alongBoundary (j : Fin n) {p : D}
    (hp : IsClosed ({p} : Set D)) (hJ : (J j).val = (D.fromSpecResidueField p).ker)
    (hE : E[j].IsExceptionalCurveOfFirstKind) :
    ¬ E[j].support ≤ (T).boundaryι.ker.support := by
  intro hle
  let π := (T).toTower.toBase
  let s := (T).boundaryι
  have hpoint (x : (alongBoundary i J).1) (hx : x ∈ E[j].support) : π x = i p := by
    have hker := D.support_ker_fromSpecResidueField_of_isClosed hp
    simpa only [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage,
      support_map_of_isClosedImmersion, hJ, hker, Set.image_singleton, Set.mem_singleton_iff]
      using hx
  have hrange (x : (alongBoundary i J).1) (hx : x ∈ E[j].support) : x ∈ Set.range s := by
    have hmem := hle hx
    rwa [← SetLike.mem_coe, s.support_ker, s.isClosedEmbedding.isClosed_range.closure_eq] at hmem
  refine hE.not_subsingleton_support fun x hx y hy ↦ ?_
  obtain ⟨a, rfl⟩ := hrange x hx
  obtain ⟨b, rfl⟩ := hrange y hy
  have hab := (hpoint (s a) hx).trans (hpoint (s b) hy).symm
  have hs : s ≫ π = i := (T).boundaryι_toBase
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hs] at hab
  exact congrArg s (i.injective hab)

variable (k) [IsAlgClosed k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

/-- An identification with an ordered internal blowup model of a root-free pair
gives an internal exceptional configuration on the pair, with the ordered total
exceptional classes of the given model. -/
theorem exceptional_configuration_alongBoundary_of_iso
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] (B : Y.IdealSheafData)
    (a : Y ≅ (alongBoundary i J).1)
    (ha : a.hom ≫ (T).toTower.toBase ≫ (X ↘ Spec (.of k)) = Y ↘ Spec (.of k))
    (hB : (B.comap a.inv).support = (T).boundaryι.ker.support)
    (hJ : ∀ j, ∃ p : D, IsClosed ({p} : Set D) ∧ (J j).val = (D.fromSpecResidueField p).ker)
    (hroot : ¬ ∃ (C : Scheme.{u}) (g : C ⟶ Y) (_ : IsClosedImmersion g) (_ : IsIntegral C)
      (hg : g.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range g) B.support ∧
      Chow.classIntersectionNumber k Y (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹ = -2) :
    let E (j : Fin n) := E[j].comap a.hom
    Pairwise (fun j l ↦ Disjoint ((E j).support : Set Y) (E l).support) ∧
    (∀ j, ¬ (E j).support ≤ B.support) ∧
    ∀ j, ∃ h : (E j).IsExceptionalCurveOfFirstKind,
      (LineBundleClass.mk h.isEffectiveCartier.toInvertibleSheaf)⁻¹ =
        LineBundleClass.pullback a.hom ((T).toTower.exceptionalClass j) := by
  let : (alongBoundary i J).1.Over (Spec (.of k)) :=
    ⟨(T).toTower.toBase ≫ (X ↘ Spec (.of k))⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  have hrootModel : ¬ ∃ (C : Scheme.{u}) (g : C ⟶ (alongBoundary i J).1)
      (_ : IsClosedImmersion g) (_ : IsIntegral C) (hg : g.ker.IsEffectiveCartier),
      topologicalKrullDim C = 1 ∧ Disjoint (Set.range g) (Set.range (T).boundaryι) ∧
      Chow.classIntersectionNumber k (alongBoundary i J).1
        (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹
        (LineBundleClass.mk hg.toInvertibleSheaf)⁻¹ = -2 := by
    rintro ⟨C, g, _, hC, hg, hdim, hdis, hsq⟩
    have hk : (g ≫ a.inv).ker = g.ker.comap a.hom := by
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        ((g ≫ a.inv).comap_ker_comp_of_isClosedImmersion a.hom).symm
    let h := hk.symm ▸ hg.comap a.hom
    refine hroot ⟨C, g ≫ a.inv, inferInstance, hC, h, hdim, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      rintro _ ⟨x, rfl⟩ hx
      apply Set.disjoint_left.mp hdis (Set.mem_range_self x)
      rw [← (T).boundaryι.isClosedEmbedding.isClosed_range.closure_eq,
        ← (T).boundaryι.support_ker, ← hB, support_comap,
        Closeds.coe_preimage, Set.mem_preimage]
      simpa only [Scheme.Hom.comp_apply] using hx
    · rw [LineBundleClass.mk_toInvertibleSheaf_congr h (hg.comap a.hom) hk,
        ← hg.pullback_mk_toInvertibleSheaf (hg.comap a.hom),
        ← LineBundleClass.pullback_inv, Chow.classIntersectionNumber_pullback_of_isIso]
      exact hsq
  obtain ⟨hd, hE⟩ := exceptional_configuration_alongBoundary i J k hJ hrootModel
  have hb : ((T).boundaryι.ker.comap a.hom).support = B.support := by
    rw [support_comap, ← hB, ← support_comap, ← comap_comp, Iso.hom_inv_id, comap_id]
  refine ⟨fun j l hjl ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · simpa only [support_comap, Closeds.coe_preimage] using (hd hjl).preimage a.hom
  · obtain ⟨p, hp, hj⟩ := hJ j
    intro hle
    apply exceptional_support_not_le_boundary_alongBoundary i J j hp hj (hE j).choose
    rw [← hb] at hle
    simpa only [← SetLike.coe_subset_coe, support_comap, Closeds.coe_preimage,
      a.hom.surjective.preimage_subset_preimage_iff] using hle
  · obtain ⟨h, hc, -⟩ := hE j
    let h' := h.comap_of_isIso a.hom
    refine ⟨h', ?_⟩
    rw [← h.isEffectiveCartier.pullback_mk_toInvertibleSheaf h'.isEffectiveCartier,
      ← LineBundleClass.pullback_inv, hc]

end QPainleve.BlowupTower
