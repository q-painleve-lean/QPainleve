/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Base change of ordered blowups along a boundary

A base change that is an isomorphism over the original boundary centers pulls back the
ordered ambient blowups and their strict boundary embeddings. At every stage the current
center is the image of the specified closed subscheme under the current boundary embedding.
Consequently the comparison also covers repeated centers and their infinitely near lifts.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData

namespace QPainleve.BlowupTower

universe u

variable {D D' X X' Y Y' S : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  {f : X' ⟶ X} {d : D' ⟶ D} {n : ℕ}
  {T : WithBoundary i n Y} {T' : WithBoundary i' n Y'} {g : Y' ⟶ Y}

/-- A boundary subscheme disjoint from the current center has the full inverse-image
scheme structure in the new ambient blowup. -/
theorem WithBoundary.map_center_snoc_of_disjoint (T : WithBoundary i n Y)
    (I J : D.IdealSheafData) (hI : I.IsEffectiveCartier)
    (h : Disjoint ((I.map T.boundaryι).support : Set Y) ((J.map T.boundaryι).support : Set Y)) :
    J.map (T.snoc I hI).boundaryι = (J.map T.boundaryι).comap (I.map T.boundaryι).blowupToBase := by
  let π := (I.map T.boundaryι).blowupToBase
  have hrange : Set.range (J.subschemeι ≫ T.boundaryι) = ((J.map T.boundaryι).support : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_subschemeι,
      support_map_of_isClosedImmersion]
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

/-- The boundary tower restricts to an isomorphism over every open subset of the
original surface that avoids its prescribed centers. -/
theorem isIso_toBase_restrict_alongBoundary [IsClosedImmersion i]
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}) (U : X.Opens)
    (hU : ∀ j, Disjoint (U : Set X) (((J j).val.map i).support : Set X)) :
    IsIso ((alongBoundary i J).2.toTower.toBase ∣_ U) := by
  induction n with
  | zero =>
    rw [alongBoundary_zero, WithBoundary.toTower_nil, toBase_nil]
    infer_instance
  | succ n ih =>
    let A := alongBoundary i (fun j : Fin n ↦ J j.castSucc)
    let P := A.2
    let K := (J (Fin.last n)).val
    let π := P.toTower.toBase
    have hd : Disjoint ((π ⁻¹ᵁ U) : Set A.1) ((K.map P.boundaryι).support : Set A.1) := by
      rw [support_map_of_isClosedImmersion]
      apply Set.disjoint_left.mpr
      rintro _ hx ⟨p, hp, rfl⟩
      have hmem := π.mem_preimage.mp hx
      rw [← Scheme.Hom.comp_apply, WithBoundary.boundaryι_toBase] at hmem
      exact Set.disjoint_left.mp (hU (Fin.last n)) hmem
        (by rw [support_map_of_isClosedImmersion]; exact ⟨p, hp, rfl⟩)
    have hstep := (K.map P.boundaryι).isIso_blowupToBase_restrict_of_disjoint_support hd
    have hprefix : IsIso (π ∣_ U) := ih _ fun j ↦ hU j.castSucc
    rw [alongBoundary_succ, WithBoundary.toTower_snoc, toBase_snoc, morphismRestrict_comp]
    exact IsIso.comp_isIso' hstep hprefix

/-- A boundary subscheme disjoint from every center has its full inverse image on the
final surface given by its image under the final boundary embedding. -/
theorem comap_map_toBase_alongBoundary [IsClosedImmersion i]
    (J : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}) (K : D.IdealSheafData)
    (hK : ∀ j, Disjoint ((J j).val.support : Set D) (K.support : Set D)) :
    (K.map i).comap (alongBoundary i J).2.toTower.toBase =
      K.map (alongBoundary i J).2.boundaryι := by
  induction n with
  | zero =>
    rw [alongBoundary_zero, WithBoundary.toTower_nil, toBase_nil, comap_id,
      WithBoundary.boundaryι_nil]
  | succ n ih =>
    let U := alongBoundary i (fun j : Fin n ↦ J j.castSucc)
    let P := U.2
    let A := J (Fin.last n)
    have hd : Disjoint ((A.val.map P.boundaryι).support : Set U.1)
        ((K.map P.boundaryι).support : Set U.1) := by
      rw [support_map_of_isClosedImmersion, support_map_of_isClosedImmersion]
      exact Set.disjoint_image_of_injective P.boundaryι.isClosedEmbedding.injective
        (hK (Fin.last n))
    rw [alongBoundary_succ, WithBoundary.toTower_snoc, toBase_snoc, comap_comp,
      ih _ (fun j ↦ hK j.castSucc)]
    exact (P.map_center_snoc_of_disjoint A.val K A.property hd).symm

/-- The total transform of a closed subscheme of the original boundary restricts
to the original ideal on the final boundary. -/
@[simp]
theorem WithBoundary.comap_map_toBase_boundaryι [IsClosedImmersion i]
    (T : WithBoundary i n Y) (J : D.IdealSheafData) :
    ((J.map i).comap T.toTower.toBase).comap T.boundaryι = J := by
  rw [← comap_comp, WithBoundary.boundaryι_toBase, comap_map_of_isClosedImmersion]

/-- If the ambient tower and the original boundary are pulled back, the commuting
square of the final boundary embeddings is cartesian. -/
theorem WithBoundary.isPullback_boundaryι (hi : IsPullback i' d f i)
    (hg : IsPullback g T'.toTower.toBase T.toTower.toBase f)
    (hb : T'.boundaryι ≫ g = d ≫ T.boundaryι) :
    IsPullback T'.boundaryι d g T.boundaryι :=
  (IsPullback.of_bot (by simpa only [boundaryι_toBase] using hi.flip) hb.symm hg).flip

private theorem isPullback_center (hi : i' ≫ f = d ≫ i)
    (hg : IsPullback g T'.toTower.toBase T.toTower.toBase f)
    (hb : T'.boundaryι ≫ g = d ≫ T.boundaryι)
    (s : S ⟶ D) (s' : S ⟶ D') (hs : s' ≫ d = s)
    (hiso : Set.range (s ≫ i) ⊆ f.isoLocus) :
    IsPullback (s' ≫ T'.boundaryι) (𝟙 _) g (s ≫ T.boundaryι) := by
  have hcomm : (s' ≫ T'.boundaryι) ≫ g = (𝟙 _) ≫ (s ≫ T.boundaryι) := by
    simp only [Category.assoc, hb, ← Category.assoc s' d, hs, Category.id_comp]
  have hbase : IsPullback (s' ≫ i') (𝟙 _) f (s ≫ i) := by
    refine f.isPullback_of_isIso_of_range_subset_isoLocus _ _ _ ?_ hiso
    simp only [Category.assoc, hi, ← Category.assoc s' d, hs, Category.id_comp]
  refine (IsPullback.of_bot (v₁₁ := s' ≫ T'.boundaryι)
    (v₁₂ := s ≫ T.boundaryι) ?_ hcomm.symm hg).flip
  simpa only [Category.assoc, WithBoundary.boundaryι_toBase] using hbase.flip

private theorem support_center_subset_isoLocus
    (hg : IsPullback g T'.toTower.toBase T.toTower.toBase f)
    (s : S ⟶ D) [IsClosedImmersion s] (hiso : Set.range (s ≫ i) ⊆ f.isoLocus) :
    ((s.ker.map T.boundaryι).support : Set Y) ⊆ g.isoLocus := by
  rw [map_ker, Scheme.Hom.support_ker,
    (s ≫ T.boundaryι).isClosedEmbedding.isClosed_range.closure_eq]
  rintro _ ⟨x, rfl⟩
  apply Scheme.Hom.preimage_isoLocus_le_of_isPullback hg
  apply T.toTower.toBase.mem_preimage.mpr
  rw [← Scheme.Hom.comp_apply, Category.assoc, WithBoundary.boundaryι_toBase]
  exact hiso (Set.mem_range_self x)

private theorem exists_isPullback_snoc (hi : i' ≫ f = d ≫ i)
    (hg : IsPullback g T'.toTower.toBase T.toTower.toBase f)
    (hb : T'.boundaryι ≫ g = d ≫ T.boundaryι)
    (s : S ⟶ D) [IsClosedImmersion s] (s' : S ⟶ D') (hs : s' ≫ d = s)
    (hC : s.ker.IsEffectiveCartier) (hC' : s'.ker.IsEffectiveCartier)
    (hiso : Set.range (s ≫ i) ⊆ f.isoLocus) :
    ∃ q : (s'.ker.map T'.boundaryι).blowup ⟶ (s.ker.map T.boundaryι).blowup,
      IsPullback q (T'.snoc s'.ker hC').toTower.toBase (T.snoc s.ker hC).toTower.toBase f ∧
        (T'.snoc s'.ker hC').boundaryι ≫ q = d ≫ (T.snoc s.ker hC).boundaryι := by
  let I := s.ker.map T.boundaryι
  have hcenter : I.comap g = s'.ker.map T'.boundaryι := by
    simpa only [I, map_ker] using
      (ker_eq_comap_of_isPullback _ (isPullback_center hi hg hb s s' hs hiso)).symm
  have hsupport := support_center_subset_isoLocus hg s hiso
  obtain ⟨q, hq⟩ : ∃ q : (s'.ker.map T'.boundaryι).blowup ⟶ I.blowup,
      IsPullback q (s'.ker.map T'.boundaryι).blowupToBase I.blowupToBase g := by
    generalize s'.ker.map T'.boundaryι = I' at hcenter ⊢
    subst I'
    exact ⟨_, (I.isPullback_blowupMap_of_support_subset_isoLocus g hsupport).flip⟩
  refine ⟨q, ?_, ?_⟩
  · simpa only [WithBoundary.toTower_snoc, BlowupTower.toBase_snoc] using hq.paste_vert hg
  · apply I.blowup_hom_ext
    · simpa only [I, Category.assoc, hq.w, ← Category.assoc (T'.snoc s'.ker hC').boundaryι,
        WithBoundary.boundaryι_snoc_blowupToBase] using hb
    · rw [Category.assoc, hq.w, ← Category.assoc, WithBoundary.boundaryι_snoc_blowupToBase,
        comap_comp, hcenter, comap_map_of_isClosedImmersion]
      exact hC'

/-- Ordered blowups of Cartier subschemes of a boundary commute with base change
that is an isomorphism over the original centers. The lift intertwines the final
strict-transform embeddings of the fixed boundaries. -/
theorem exists_isPullback_alongBoundary [IsClosedImmersion i] [IsClosedImmersion i']
    (hi : i' ≫ f = d ≫ i) {S : Fin n → Scheme.{u}}
    (s : ∀ j, S j ⟶ D) (s' : ∀ j, S j ⟶ D') (hs : ∀ j, s' j ≫ d = s j)
    [∀ j, IsClosedImmersion (s j)]
    (hC : ∀ j, (s j).ker.IsEffectiveCartier) (hC' : ∀ j, (s' j).ker.IsEffectiveCartier)
    (hiso : ∀ j, Set.range (s j ≫ i) ⊆ f.isoLocus) :
    let A := alongBoundary i (fun j ↦ ⟨(s j).ker, hC j⟩)
    let A' := alongBoundary i' (fun j ↦ ⟨(s' j).ker, hC' j⟩)
    ∃ q : A'.1 ⟶ A.1, IsPullback q A'.2.toTower.toBase A.2.toTower.toBase f ∧
      A'.2.boundaryι ≫ q = d ≫ A.2.boundaryι := by
  dsimp only
  induction n with
  | zero =>
    rw [alongBoundary_zero i', alongBoundary_zero i]
    simp only [WithBoundary.toTower_nil, BlowupTower.toBase_nil, WithBoundary.boundaryι_nil]
    exact ⟨f, IsPullback.of_vert_isIso ⟨by simp⟩, hi⟩
  | succ n ih =>
    obtain ⟨g, hg, hb⟩ := ih (fun j ↦ s j.castSucc) (fun j ↦ s' j.castSucc)
      (fun j ↦ hs j.castSucc) (fun j ↦ hC j.castSucc) (fun j ↦ hC' j.castSucc)
      (fun j ↦ hiso j.castSucc)
    rw [alongBoundary_succ i', alongBoundary_succ i]
    let j := Fin.last n
    exact exists_isPullback_snoc hi hg hb (s j) (s' j) (hs j) (hC j) (hC' j) (hiso j)

end QPainleve.BlowupTower
