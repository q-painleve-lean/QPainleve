/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Class
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard

import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Reordering blowups along a fixed boundary

Two disjoint Cartier centers on the boundary can be blown up in either order.
The resulting isomorphism commutes with the projection and the strict-transform boundary
and matches the two exceptional classes with their center labels.
It extends through the rest of the ordered centers by naturality, so any permutation of a
family with disjoint supports for distinct ideals gives an isomorphic surface. A center
can occur several times.

The comparison uses `Scheme.IdealSheafData.blowupCommOfDisjoint` and
`Scheme.Hom.isPullback_of_isIso_of_range_subset_isoLocus` for the actual center subschemes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry LineBundleClass

namespace QPainleve.BlowupTower

universe u

variable {D X Y : Scheme.{u}} {i : D ⟶ X} {n : ℕ}

namespace WithBoundary

variable (T : WithBoundary i n Y) (I J : D.IdealSheafData)
  (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)

private theorem support_map_boundaryι (K : D.IdealSheafData) :
    ((K.map T.boundaryι).support : Set Y) = T.boundaryι '' (K.support : Set D) := by
  rw [support_map, Closeds.coe_closure]
  exact (T.boundaryι.isClosedEmbedding.isClosedMap _ K.support.isClosed).closure_eq

private theorem disjoint_support_map
    (h : Disjoint (I.support : Set D) (J.support : Set D)) :
    Disjoint ((I.map T.boundaryι).support : Set Y) ((J.map T.boundaryι).support : Set Y) := by
  rw [T.support_map_boundaryι, T.support_map_boundaryι]
  exact Set.disjoint_image_of_injective T.boundaryι.isClosedEmbedding.injective h

include hI in
private theorem map_center_snoc_of_disjoint
    (h : Disjoint ((I.map T.boundaryι).support : Set Y)
      ((J.map T.boundaryι).support : Set Y)) :
    J.map (T.snoc I hI).boundaryι = (J.map T.boundaryι).comap (I.map T.boundaryι).blowupToBase := by
  let π := (I.map T.boundaryι).blowupToBase
  have hrange : Set.range (J.subschemeι ≫ T.boundaryι) = ((J.map T.boundaryι).support : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_subschemeι,
      T.support_map_boundaryι]
  have hlocal : Set.range (J.subschemeι ≫ T.boundaryι) ⊆ π.isoLocus := by
    rw [hrange]
    exact fun _ hx ↦ (π.le_isoLocus_iff.mpr
      (I.map T.boundaryι).isIso_blowupToBase_restrict_compl_support)
      (Set.disjoint_right.mp h hx)
  have hp : IsPullback (J.subschemeι ≫ (T.snoc I hI).boundaryι) (𝟙 _) π
      (J.subschemeι ≫ T.boundaryι) := by
    apply π.isPullback_of_isIso_of_range_subset_isoLocus
    · simp [π]
    · exact hlocal
  simpa only [← map_ker, ker_subschemeι] using
    ker_eq_comap_of_isPullback (J.subschemeι ≫ T.boundaryι) hp

include hI hJ in
private theorem boundaryι_snoc_blowupMap
    {e : (J.map (T.snoc I hI).boundaryι).blowup ≅
      ((J.map T.boundaryι).comap (I.map T.boundaryι).blowupToBase).blowup}
    (he : e.hom ≫ ((J.map T.boundaryι).comap (I.map T.boundaryι).blowupToBase).blowupToBase =
      (J.map (T.snoc I hI).boundaryι).blowupToBase) :
    ((T.snoc I hI).snoc J hJ).boundaryι ≫ e.hom ≫
      (J.map T.boundaryι).blowupMap (I.map T.boundaryι).blowupToBase =
        (T.snoc J hJ).boundaryι := by
  have hbase : (((T.snoc I hI).snoc J hJ).boundaryι ≫ e.hom ≫
      (J.map T.boundaryι).blowupMap (I.map T.boundaryι).blowupToBase) ≫
      (J.map T.boundaryι).blowupToBase = T.boundaryι := by
    rw [Category.assoc, Category.assoc, blowupMap_blowupToBase, ← Category.assoc e.hom, he]
    simp
  apply (J.map T.boundaryι).blowup_hom_ext
  · simpa using hbase
  · rw [hbase]
    simpa using hJ

/-- Interchanging two disjoint Cartier centers of the fixed boundary preserves the
projection, the strict boundary, and the two exceptional classes with their labels exchanged. -/
theorem exists_iso_snoc_snoc_of_disjoint (h : Disjoint (I.support : Set D) (J.support : Set D)) :
    let TI := T.snoc I hI
    let TJ := T.snoc J hJ
    let A := I.map T.boundaryι
    let B := J.map T.boundaryι
    let B' := J.map TI.boundaryι
    let A' := I.map TJ.boundaryι
    ∃ e : B'.blowup ≅ A'.blowup,
      B'.blowupToBase ≫ A.blowupToBase = e.hom ≫ A'.blowupToBase ≫ B.blowupToBase ∧
      (TI.snoc J hJ).boundaryι ≫ e.hom = (TJ.snoc I hI).boundaryι ∧
      pullback e.hom A'.blowupExceptionalClass = pullback B'.blowupToBase A.blowupExceptionalClass ∧
      pullback e.hom (pullback A'.blowupToBase B.blowupExceptionalClass) =
        B'.blowupExceptionalClass := by
  let A := I.map T.boundaryι
  let B := J.map T.boundaryι
  have hd : Disjoint (A.support : Set Y) (B.support : Set Y) := T.disjoint_support_map I J h
  have hI' : (B.comap A.blowupToBase).comap (Iso.refl _).hom = J.map (T.snoc I hI).boundaryι := by
    simpa only [Iso.refl_hom, comap_id] using (T.map_center_snoc_of_disjoint I J hI hd).symm
  have hJ' : (A.comap B.blowupToBase).comap (Iso.refl _).hom = I.map (T.snoc J hJ).boundaryι := by
    simpa only [Iso.refl_hom, comap_id] using (T.map_center_snoc_of_disjoint J I hJ hd.symm).symm
  let eI := (B.comap A.blowupToBase).blowupIso (Iso.refl _) hI'
  let eJ := (A.comap B.blowupToBase).blowupIso (Iso.refl _) hJ'
  have hIproj : eI.hom ≫ (B.comap A.blowupToBase).blowupToBase =
      (J.map (T.snoc I hI).boundaryι).blowupToBase := by simp [eI]
  have hJproj : eJ.hom ≫ (A.comap B.blowupToBase).blowupToBase =
      (I.map (T.snoc J hJ).boundaryι).blowupToBase := by simp [eJ]
  have hIex : pullback eI.hom (B.comap A.blowupToBase).blowupExceptionalClass =
      (J.map (T.snoc I hI).boundaryι).blowupExceptionalClass :=
    (B.comap A.blowupToBase).pullback_blowupExceptionalClass (Iso.refl _) hI'
  have hJex : pullback eJ.hom (A.comap B.blowupToBase).blowupExceptionalClass =
      (I.map (T.snoc J hJ).boundaryι).blowupExceptionalClass :=
    (A.comap B.blowupToBase).pullback_blowupExceptionalClass (Iso.refl _) hJ'
  refine ⟨eI ≪≫ A.blowupCommOfDisjoint B hd ≪≫ eJ.symm, ?_, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hJproj,
      Iso.inv_hom_id_assoc, blowupCommOfDisjoint_hom_blowupToBase_assoc]
    rw [blowupMap_blowupToBase, ← Category.assoc, hIproj]
  · rw [← cancel_mono eJ.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply (A.isPullback_blowupMap_of_disjoint B hd).hom_ext
    · simp only [Category.assoc, blowupCommOfDisjoint_hom_blowupToBase]
      rw [T.boundaryι_snoc_blowupMap I J hI hJ hIproj, hJproj,
        boundaryι_snoc_blowupToBase]
    · simp only [Category.assoc, blowupCommOfDisjoint_hom_blowupMap, hIproj,
        boundaryι_snoc_blowupToBase]
      exact (T.boundaryι_snoc_blowupMap J I hJ hI hJproj).symm
  · rw [← hJex, ← pullback_blowupExceptionalClass_blowupMap A B.blowupToBase]
    simp only [Iso.trans_hom, Iso.symm_hom, pullback_comp, Category.assoc,
      Iso.inv_hom_id_assoc, blowupCommOfDisjoint_hom_blowupMap, hIproj, A]
  · simp only [← hJproj, Iso.trans_hom, Iso.symm_hom, pullback_comp, Category.assoc,
      Iso.inv_hom_id_assoc, blowupCommOfDisjoint_hom_blowupToBase]
    rwa [← pullback_comp, pullback_blowupExceptionalClass_blowupMap]

end WithBoundary

private abbrev Center (D : Scheme.{u}) := {J : D.IdealSheafData // J.IsEffectiveCartier}

private theorem WithBoundary.exists_iso_snoc_of_boundaryι_eq {Y' : Scheme.{u}} {m : ℕ}
    {T : WithBoundary i n Y} {U : WithBoundary i m Y'} (e : Y ≅ Y')
    (hb : T.boundaryι ≫ e.hom = U.boundaryι) (J : Center D) :
    let I := J.val.map T.boundaryι
    let K := J.val.map U.boundaryι
    ∃ f : I.blowup ≅ K.blowup,
      f.hom ≫ K.blowupToBase = I.blowupToBase ≫ e.hom ∧
      (T.snoc J.val J.property).boundaryι ≫ f.hom = (U.snoc J.val J.property).boundaryι ∧
      pullback f.hom K.blowupExceptionalClass = I.blowupExceptionalClass := by
  let K := J.val.map U.boundaryι
  have hb' : T.boundaryι ≫ e.hom = (Iso.refl D).hom ≫ U.boundaryι := by simpa using hb
  have hJ : J.val.comap (Iso.refl D).hom = J.val := by simp
  let hK := T.comap_center_eq J.val e (Iso.refl D) hb' J.val hJ
  refine ⟨K.blowupIso e hK, K.blowupIso_hom_blowupToBase e hK, ?_,
    K.pullback_blowupExceptionalClass e hK⟩
  simpa only [Iso.refl_hom, Category.id_comp] using
    T.boundaryι_snoc_blowupIso_hom J.val e (Iso.refl D) hb' J.val hJ J.property J.property

-- The length is packaged so the list operations can append to any prefix tower.
private abbrev BoundaryTower (i : D ⟶ X) := Σ n, Σ Y, WithBoundary i n Y

namespace BoundaryTower

private def snoc (T : BoundaryTower i) (J : Center D) : BoundaryTower i :=
  ⟨_, _, T.2.2.snoc J.val J.property⟩

private def extend (T : BoundaryTower i) (l : List (Center D)) : BoundaryTower i :=
  l.foldl snoc T

private theorem extend_concat (T : BoundaryTower i) (l : List (Center D)) (J : Center D) :
    T.extend (l.concat J) = (T.extend l).snoc J := by
  simp [extend, List.concat_eq_append, List.foldl_append]

-- These comparisons remember both maps out of the center ordering: the projection to
-- the base and the embedding of the fixed boundary into the final surface.
private def OverBoundaryIso (T U : BoundaryTower i) : Prop :=
  ∃ e : T.2.1 ≅ U.2.1,
    e.hom ≫ U.2.2.toTower.toBase = T.2.2.toTower.toBase ∧
    T.2.2.boundaryι ≫ e.hom = U.2.2.boundaryι

private theorem OverBoundaryIso.refl (T : BoundaryTower i) : OverBoundaryIso T T :=
  ⟨Iso.refl _, by simp, by simp⟩

private theorem OverBoundaryIso.trans {T U V : BoundaryTower i}
    (h₁ : OverBoundaryIso T U) (h₂ : OverBoundaryIso U V) : OverBoundaryIso T V := by
  obtain ⟨e, he, hbe⟩ := h₁
  obtain ⟨f, hf, hbf⟩ := h₂
  refine ⟨e ≪≫ f, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc, hf, he]
  · simp only [Iso.trans_hom, ← Category.assoc, hbe, hbf]

private theorem OverBoundaryIso.snoc {T U : BoundaryTower i} (h : OverBoundaryIso T U)
    (J : Center D) : OverBoundaryIso (T.snoc J) (U.snoc J) := by
  obtain ⟨e, he, hb⟩ := h
  obtain ⟨e', he', hb', -⟩ :=
    WithBoundary.exists_iso_snoc_of_boundaryι_eq (T := T.2.2) (U := U.2.2) e hb J
  unfold OverBoundaryIso BoundaryTower.snoc
  refine ⟨e', ?_, hb'⟩
  simp only [WithBoundary.toTower_snoc, toBase_snoc, ← Category.assoc]
  rw [he', Category.assoc, he]

private theorem OverBoundaryIso.extend {T U : BoundaryTower i} (h : OverBoundaryIso T U)
    (l : List (Center D)) : OverBoundaryIso (T.extend l) (U.extend l) := by
  induction l generalizing T U with
  | nil => exact h
  | cons J l ih => exact ih (h.snoc J)

private theorem overBoundaryIso_swap (T : BoundaryTower i) (J K : Center D)
    (h : Disjoint (J.val.support : Set D) (K.val.support : Set D)) :
    OverBoundaryIso ((T.snoc J).snoc K) ((T.snoc K).snoc J) := by
  obtain ⟨e, he, hb, -, -⟩ :=
    T.2.2.exists_iso_snoc_snoc_of_disjoint J.val K.val J.property K.property h
  refine ⟨e, ?_, hb⟩
  simpa only [snoc, WithBoundary.toTower_snoc, toBase_snoc, Category.assoc] using
    congrArg (· ≫ T.2.2.toTower.toBase) he.symm

private theorem overBoundaryIso_extend_perm (T : BoundaryTower i) {l l' : List (Center D)}
    (h : l.Perm l') (hd : ∀ J ∈ l, ∀ K ∈ l, J ≠ K →
      Disjoint (J.val.support : Set D) (K.val.support : Set D)) :
    OverBoundaryIso (T.extend l) (T.extend l') := by
  classical
  induction h generalizing T with
  | nil => exact OverBoundaryIso.refl _
  | cons J h ih =>
    exact ih (T.snoc J) fun K hK L hL ↦ hd K (.tail _ hK) L (.tail _ hL)
  | swap J K l =>
    by_cases he : K = J
    · subst K
      exact OverBoundaryIso.refl _
    · exact (T.overBoundaryIso_swap K J (hd K (by simp) J (by simp) he)).extend l
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ T hd).trans (ih₂ T fun J hJ K hK ↦ hd J (h₁.mem_iff.mpr hJ) K
      (h₁.mem_iff.mpr hK))

private theorem extend_ofFn [IsClosedImmersion i]
    (J : Fin n → Center D) :
    (extend ⟨0, X, WithBoundary.nil i⟩ (List.ofFn J) : BoundaryTower i) =
      ⟨n, (alongBoundary i J).1, (alongBoundary i J).2⟩ := by
  induction n with
  | zero => simp [extend, alongBoundary_zero]
  | succ n ih =>
    rw [List.ofFn_succ', extend_concat, ih, alongBoundary_succ]
    rfl

end BoundaryTower

/-- Reordering an ordered family of Cartier centers with disjoint supports for distinct
ideals gives an isomorphism over the original surface and preserves the strict boundary.
Repeated occurrences of the same ideal are allowed and give successive blowups above that
center. -/
theorem exists_iso_alongBoundary_perm_of_disjoint [IsClosedImmersion i] {m : ℕ}
    (J : Fin n → {K : D.IdealSheafData // K.IsEffectiveCartier})
    (K : Fin m → {K : D.IdealSheafData // K.IsEffectiveCartier})
    (h : (List.ofFn J).Perm (List.ofFn K))
    (hd : ∀ a b, J a ≠ J b → Disjoint ((J a).val.support : Set D) ((J b).val.support : Set D)) :
    ∃ e : (alongBoundary i J).1 ≅ (alongBoundary i K).1,
      e.hom ≫ (alongBoundary i K).2.toTower.toBase = (alongBoundary i J).2.toTower.toBase ∧
      (alongBoundary i J).2.boundaryι ≫ e.hom = (alongBoundary i K).2.boundaryι := by
  have hp := BoundaryTower.overBoundaryIso_extend_perm
    (⟨0, X, WithBoundary.nil i⟩ : BoundaryTower i) h (by
      intro A hA B hB
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hA
      obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hB
      exact hd a b)
  rw [BoundaryTower.extend_ofFn, BoundaryTower.extend_ofFn] at hp
  exact hp

section Labeled

private def Reordered (T U : Σ Y, WithBoundary i n Y) (σ : Fin n → Fin n) : Prop :=
  ∃ e : T.1 ≅ U.1,
    e.hom ≫ U.2.toTower.toBase = T.2.toTower.toBase ∧
    T.2.boundaryι ≫ e.hom = U.2.boundaryι ∧
    ∀ j, pullback e.hom (U.2.toTower.exceptionalClass j) = T.2.toTower.exceptionalClass (σ j)

private theorem Reordered.trans {T U V : Σ Y, WithBoundary i n Y} {σ τ : Fin n → Fin n}
    (h₀ : Reordered T U σ) (h₁ : Reordered U V τ) : Reordered T V (σ ∘ τ) := by
  obtain ⟨e, he, hbe, hEe⟩ := h₀
  obtain ⟨f, hf, hbf, hEf⟩ := h₁
  exact ⟨e ≪≫ f, by simp [hf, he], by simp [← Category.assoc, hbe, hbf],
    fun j ↦ by rw [Iso.trans_hom, ← pullback_comp, hEf, hEe, Function.comp_apply]⟩

private theorem Reordered.snoc {T U : Σ Y, WithBoundary i n Y} {σ : Fin n → Fin n}
    (h : Reordered T U σ) (J : Center D) :
    Reordered ⟨_, T.2.snoc J.val J.property⟩ ⟨_, U.2.snoc J.val J.property⟩
      (Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)) := by
  obtain ⟨e, he, hb, hE⟩ := h
  obtain ⟨f, hf, hbf, hEf⟩ := WithBoundary.exists_iso_snoc_of_boundaryι_eq e hb J
  refine ⟨f, ?_, hbf, ?_⟩
  · simp only [WithBoundary.toTower_snoc, toBase_snoc, ← Category.assoc]
    rw [hf, Category.assoc, he]
  · intro j
    refine Fin.lastCases ?_ (fun a ↦ ?_) j
    · simp only [Fin.snoc_last, WithBoundary.toTower_snoc, exceptionalClass_snoc_last,
        ← blowupExceptionalClass_def]
      exact hEf
    · simp only [Fin.snoc_castSucc, Function.comp_apply, WithBoundary.toTower_snoc,
        exceptionalClass_snoc_castSucc]
      rw [pullback_comp, hf, ← pullback_comp, hE]

-- The last two indices are exchanged and the previous labels stay fixed.
private def swapLastTwo (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.snoc (Fin.snoc (Fin.castSucc ∘ Fin.castSucc) (Fin.last (n + 1))) (Fin.last n).castSucc

private theorem reordered_swapLastTwo (T : Σ Y, WithBoundary i n Y) (J K : Center D)
    (h : Disjoint (J.val.support : Set D) (K.val.support : Set D)) :
    Reordered ⟨_, (T.2.snoc J.val J.property).snoc K.val K.property⟩
      ⟨_, (T.2.snoc K.val K.property).snoc J.val J.property⟩ (swapLastTwo n) := by
  obtain ⟨e, he, hb, hJ, hK⟩ :=
    T.2.exists_iso_snoc_snoc_of_disjoint J.val K.val J.property K.property h
  refine ⟨e, ?_, hb, ?_⟩
  · simpa only [WithBoundary.toTower_snoc, toBase_snoc, Category.assoc] using
      congrArg (· ≫ T.2.toTower.toBase) he.symm
  · intro j
    refine Fin.lastCases ?_ (fun a ↦ Fin.lastCases ?_ (fun b ↦ ?_) a) j
    · simpa only [swapLastTwo, Fin.snoc_last, WithBoundary.toTower_snoc,
        exceptionalClass_snoc_castSucc, exceptionalClass_snoc_last, ← blowupExceptionalClass_def]
        using hJ
    · simpa only [swapLastTwo, Fin.snoc_castSucc, Fin.snoc_last, WithBoundary.toTower_snoc,
        exceptionalClass_snoc_castSucc, exceptionalClass_snoc_last, ← blowupExceptionalClass_def]
        using hK
    · simp only [swapLastTwo, Fin.snoc_castSucc, Function.comp_apply, WithBoundary.toTower_snoc,
        exceptionalClass_snoc_castSucc, pullback_comp, ← he]

variable [IsClosedImmersion i]

private theorem alongBoundary_eq_snoc {J : Fin (n + 1) → Center D}
    {F : Fin n → Center D} {C : Center D}
    (hp : (fun j : Fin n ↦ J j.castSucc) = F) (hl : J (Fin.last n) = C) :
    alongBoundary i J = ⟨_, (alongBoundary i F).2.snoc C.val C.property⟩ := by
  subst F
  subst C
  exact alongBoundary_succ i J

private theorem reordered_alongBoundary_swapLastTwo (J : Fin (n + 2) → Center D)
    (h : Disjoint ((J (Fin.last n).castSucc).val.support : Set D)
      ((J (Fin.last (n + 1))).val.support : Set D)) :
    Reordered (alongBoundary i J) (alongBoundary i (J ∘ swapLastTwo n)) (swapLastTwo n) := by
  have hprefix :
      (fun j : Fin n ↦ (J ∘ swapLastTwo n) j.castSucc.castSucc) =
        fun j ↦ J j.castSucc.castSucc := by
    funext j
    simp [swapLastTwo]
  have hlast : (J ∘ swapLastTwo n) (Fin.last (n + 1)) = J (Fin.last n).castSucc := by
    simp [swapLastTwo]
  have hnext : (J ∘ swapLastTwo n) (Fin.last n).castSucc = J (Fin.last (n + 1)) := by
    simp [swapLastTwo]
  rw [alongBoundary_succ i J, alongBoundary_eq_snoc (i := i) rfl hlast,
    alongBoundary_succ i (fun j : Fin (n + 1) ↦ J j.castSucc),
    alongBoundary_eq_snoc (i := i) hprefix hnext]
  exact reordered_swapLastTwo (alongBoundary i (fun j : Fin n ↦ J j.castSucc.castSucc))
    (J (Fin.last n).castSucc) (J (Fin.last (n + 1))) h

private theorem Reordered.alongBoundary_snoc {J : Fin (n + 1) → Center D} {σ : Fin n → Fin n}
    (h : Reordered (alongBoundary i (J ∘ Fin.castSucc))
      (alongBoundary i (J ∘ Fin.castSucc ∘ σ)) σ) :
    let τ := Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)
    Reordered (alongBoundary i J) (alongBoundary i (J ∘ τ)) τ := by
  dsimp only
  have hprefix :
      (fun j : Fin n ↦ (J ∘ Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)) j.castSucc) =
        J ∘ Fin.castSucc ∘ σ := by
    funext j
    simp
  have hlast : (J ∘ Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)) (Fin.last n) =
      J (Fin.last n) := by simp
  rw [alongBoundary_succ i J, alongBoundary_eq_snoc (i := i) hprefix hlast]
  exact h.snoc (J (Fin.last n))

private theorem reordered_alongBoundary_moveToFront {n : ℕ} (J : Fin (n + 1) → Center D)
    (k : Fin (n + 1))
    (h : ∀ j < k, Disjoint ((J j).val.support : Set D) ((J k).val.support : Set D)) :
    let σ := Fin.cons k k.succAbove
    Reordered (alongBoundary i J) (alongBoundary i (J ∘ σ)) σ := by
  induction n with
  | zero =>
    have hσ : Fin.cons k k.succAbove = id := by
      funext j
      rw [Fin.eq_zero j, Fin.cons_zero, Fin.eq_zero k, id_eq]
    have hrefl : Reordered (alongBoundary i J) (alongBoundary i J) id :=
      ⟨Iso.refl _, by simp, by simp, fun _ ↦ by simp⟩
    simpa only [hσ, Function.comp_id] using hrefl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k ↦ ?_) k h
    · intro h
      -- Swap the last center into the prefix before applying the induction hypothesis.
      let τ := swapLastTwo n
      have hswap := reordered_alongBoundary_swapLastTwo (i := i) J
        (h (Fin.last n).castSucc (Fin.castSucc_lt_last _))
      have hrec := ih (J ∘ τ ∘ Fin.castSucc) (Fin.last n) (by
        intro j hj
        obtain ⟨a, rfl⟩ := Fin.eq_castSucc_of_ne_last hj.ne
        simpa [τ, swapLastTwo] using h a.castSucc.castSucc (Fin.castSucc_lt_last _))
      have hcomp := hswap.trans hrec.alongBoundary_snoc
      have hindex : τ ∘ Fin.snoc (Fin.castSucc ∘ Fin.cons (Fin.last n) (Fin.last n).succAbove)
          (Fin.last (n + 1)) =
          Fin.cons (Fin.last (n + 1)) (Fin.last (n + 1)).succAbove := by
        funext j
        refine Fin.cases ?_ (fun a ↦ Fin.lastCases ?_ (fun b ↦ ?_) a) j
        · simp [τ, swapLastTwo]
        · simp [τ, swapLastTwo]
        · rw [← Fin.castSucc_succ]
          simp only [τ, swapLastTwo, Function.comp_apply, Fin.snoc_castSucc, Fin.cons_succ,
            Fin.succAbove_last]
          rw [Fin.castSucc_succ, Fin.cons_succ]
      simpa only [Function.comp_assoc, ← hindex] using hcomp
    · intro h
      have hrec := (ih (J ∘ Fin.castSucc) k
        (fun j hj ↦ h j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hj))).alongBoundary_snoc
      have hindex : Fin.snoc (Fin.castSucc ∘ Fin.cons k k.succAbove) (Fin.last (n + 1)) =
          Fin.cons (α := fun _ : Fin (n + 2) ↦ Fin (n + 2)) k.castSucc k.castSucc.succAbove := by
        funext j
        refine Fin.cases ?_ (fun a ↦ Fin.lastCases ?_ (fun b ↦ ?_) a) j
        · simp
        · simp
        · rw [← Fin.castSucc_succ]
          simp only [Fin.snoc_castSucc, Function.comp_apply, Fin.cons_succ]
          rw [Fin.castSucc_succ, Fin.cons_succ, Fin.castSucc_succAbove_castSucc]
      simpa only [hindex] using hrec

/-- A center disjoint from all preceding centers may be moved to the front of an ordered
boundary blowup tower. The remaining centers keep their relative order, and later centers
may have the same support as the selected center. The isomorphism is over the base, identifies
the strict boundaries, and pulls back the full Picard marking by the induced reindexing. -/
theorem exists_iso_alongBoundary_move_to_front
    (J : Fin (n + 1) → {I : D.IdealSheafData // I.IsEffectiveCartier}) (k : Fin (n + 1))
    (h : ∀ j < k, Disjoint ((J j).val.support : Set D) ((J k).val.support : Set D)) :
    let σ := Fin.cons k k.succAbove
    let A := alongBoundary i J
    let B := alongBoundary i (J ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass X)) (b : Fin (n + 1) → ℤ),
        pullback e.hom (B.2.toTower.picardHom (a, b ∘ σ)).toMul =
          (A.2.toTower.picardHom (a, b)).toMul := by
  let q := (finSuccEquiv' (0 : Fin (n + 1))).trans (finSuccEquiv' k).symm
  have hq : (q : Fin (n + 1) → Fin (n + 1)) = Fin.cons k k.succAbove := by
    funext j
    refine Fin.cases (by simp [q]) (fun j ↦ ?_) j
    have hj : finSuccEquiv' (0 : Fin (n + 1)) j.succ = some j := by
      simpa only [Fin.succAbove_zero] using finSuccEquiv'_succAbove (0 : Fin (n + 1)) j
    simp [q, hj]
  obtain ⟨e, he, hb, hE⟩ := reordered_alongBoundary_moveToFront (i := i) J k h
  refine ⟨e, he, hb, fun a b ↦ ?_⟩
  rw [picardHom_apply_toMul, picardHom_apply_toMul, pullback_mul, pullback_comp, he]
  congr 1
  rw [← pullbackHom_apply (f := e.hom), map_prod]
  simp only [pullbackHom_apply, pullback_zpow, hE, ← hq, Function.comp_apply]
  exact Fintype.prod_equiv q _ _ (fun _ ↦ rfl)

end Labeled

end QPainleve.BlowupTower
