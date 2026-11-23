/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary

import Mathlib.Data.List.OfFn
import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion

/-!
# Reordering blowups along a fixed boundary

Two disjoint Cartier centers on the boundary can be blown up in either order.
The resulting isomorphism commutes with the projection and the strict-transform boundary.
It extends through the rest of the ordered centers by naturality, so any permutation of a
family with disjoint supports for distinct ideals gives an isomorphic surface. A center
can occur several times.

The comparison uses `Scheme.IdealSheafData.blowupCommOfDisjoint` and
`WithBoundary.map_center_snoc_of_disjoint` for the actual center subschemes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower

universe u

variable {D X Y : Scheme.{u}} {i : D ⟶ X} {n : ℕ}

namespace WithBoundary

variable (T : WithBoundary i n Y) (I J : D.IdealSheafData)
  (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)

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

/-- Two disjoint Cartier centers of the fixed boundary can be blown up in either order.
The comparison is over the previous surface and identifies the two strict boundaries. -/
theorem exists_iso_snoc_snoc_of_disjoint (h : Disjoint (I.support : Set D) (J.support : Set D)) :
    let TI := T.snoc I hI
    let TJ := T.snoc J hJ
    ∃ e : (J.map TI.boundaryι).blowup ≅ (I.map TJ.boundaryι).blowup,
      (J.map TI.boundaryι).blowupToBase ≫ (I.map T.boundaryι).blowupToBase =
        e.hom ≫ (I.map TJ.boundaryι).blowupToBase ≫ (J.map T.boundaryι).blowupToBase ∧
      (TI.snoc J hJ).boundaryι ≫ e.hom = (TJ.snoc I hI).boundaryι := by
  let A := I.map T.boundaryι
  let B := J.map T.boundaryι
  have hd : Disjoint (A.support : Set Y) (B.support : Set Y) := by
    rw [I.support_map_of_isClosedImmersion, J.support_map_of_isClosedImmersion]
    exact Set.disjoint_image_of_injective T.boundaryι.isClosedEmbedding.injective h
  let eI := (B.comap A.blowupToBase).blowupIso (Iso.refl _) (by
    simpa only [Iso.refl_hom, comap_id] using (T.map_center_snoc_of_disjoint I J hI hd).symm)
  let eJ := (A.comap B.blowupToBase).blowupIso (Iso.refl _) (by
    simpa only [Iso.refl_hom, comap_id] using (T.map_center_snoc_of_disjoint J I hJ hd.symm).symm)
  have hIproj : eI.hom ≫ (B.comap A.blowupToBase).blowupToBase =
      (J.map (T.snoc I hI).boundaryι).blowupToBase := by simp [eI]
  have hJproj : eJ.hom ≫ (A.comap B.blowupToBase).blowupToBase =
      (I.map (T.snoc J hJ).boundaryι).blowupToBase := by simp [eJ]
  refine ⟨eI ≪≫ A.blowupCommOfDisjoint B hd ≪≫ eJ.symm, ?_, ?_⟩
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

end WithBoundary

private abbrev Center (D : Scheme.{u}) := {J : D.IdealSheafData // J.IsEffectiveCartier}

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
  have hb' : T.2.2.boundaryι ≫ e.hom = (Iso.refl D).hom ≫ U.2.2.boundaryι := by simpa using hb
  have hJ : J.val.comap (Iso.refl D).hom = J.val := by simp
  let K := J.val.map U.2.2.boundaryι
  let e' := K.blowupIso e (T.2.2.comap_center_eq J.val e (Iso.refl D) hb' J.val hJ)
  unfold OverBoundaryIso BoundaryTower.snoc
  dsimp only
  refine ⟨e', ?_, ?_⟩
  · rw [WithBoundary.toTower_snoc, WithBoundary.toTower_snoc, toBase_snoc, toBase_snoc]
    simp only [e', K, blowupIso_hom_blowupToBase_assoc, he]
  · simpa only [Iso.refl_hom, Category.id_comp] using
      T.2.2.boundaryι_snoc_blowupIso_hom J.val e (Iso.refl D) hb' J.val hJ J.property J.property

private theorem OverBoundaryIso.extend {T U : BoundaryTower i} (h : OverBoundaryIso T U)
    (l : List (Center D)) : OverBoundaryIso (T.extend l) (U.extend l) := by
  induction l generalizing T U with
  | nil => exact h
  | cons J l ih => exact ih (h.snoc J)

private theorem overBoundaryIso_swap (T : BoundaryTower i) (J K : Center D)
    (h : Disjoint (J.val.support : Set D) (K.val.support : Set D)) :
    OverBoundaryIso ((T.snoc J).snoc K) ((T.snoc K).snoc J) := by
  obtain ⟨e, he, hb⟩ :=
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

end QPainleve.BlowupTower
