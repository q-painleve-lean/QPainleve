/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.Blowup.Pullback
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Base change of ordered blowups along a boundary

A base change that is an isomorphism over the original boundary centers pulls back the
ordered ambient blowups and their strict boundary embeddings. At every stage the current
center is the image of the specified closed subscheme under the current boundary embedding.
Consequently the comparison also covers repeated centers and their infinitely near lifts.
When the new boundary is the reduced inverse image, the comparison recovers each
transported center as a pullback and identifies the final reduced boundary.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData
open TopologicalSpace

namespace QPainleve.BlowupTower

universe u

variable {D D' X X' Y Y' S : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  {f : X' ⟶ X} {d : D' ⟶ D} {n : ℕ}
  {T : WithBoundary i n Y} {T' : WithBoundary i' n Y'} {g : Y' ⟶ Y}

/-- An ordered boundary blowup tower is an isomorphism over any open avoiding
the images of the prescribed centers on the original boundary. -/
theorem isIso_toBase_restrict_alongBoundary (i : D ⟶ X) [IsClosedImmersion i]
    (J : Fin n → {A : D.IdealSheafData // A.IsEffectiveCartier}) (U : X.Opens)
    (hU : ∀ j, Disjoint (U : Set X) (i '' ((J j).val.support : Set D))) :
    IsIso ((alongBoundary i J).2.toTower.toBase ∣_ U) := by
  induction n with
  | zero =>
    rw [alongBoundary_zero i J, WithBoundary.toTower_nil, toBase_nil]
    infer_instance
  | succ n ih =>
    let B := alongBoundary i (fun j : Fin n ↦ J j.castSucc)
    let T := B.2
    let A := (J (Fin.last n)).val
    let I := A.map T.boundaryι
    have hT : IsIso (T.toTower.toBase ∣_ U) := ih _ (fun j ↦ hU j.castSucc)
    have hI : Disjoint (↑(T.toTower.toBase ⁻¹ᵁ U) : Set B.1) (I.support : Set B.1) := by
      rw [support_map, Closeds.coe_closure,
        (T.boundaryι.isClosedEmbedding.isClosedMap _ A.support.isClosed).closure_eq]
      apply Set.disjoint_left.mpr
      rintro x hx ⟨y, hy, hyx⟩
      have hx' := T.toTower.toBase.mem_preimage.mp hx
      rw [← hyx, ← Scheme.Hom.comp_apply, WithBoundary.boundaryι_toBase] at hx'
      exact Set.disjoint_left.mp (hU (Fin.last n)) hx' ⟨y, hy, rfl⟩
    rw [alongBoundary_succ i, WithBoundary.toTower_snoc, toBase_snoc, morphismRestrict_comp]
    exact IsIso.comp_isIso' (I.isIso_blowupToBase_restrict_of_disjoint_support hI) hT

/-- A point outside the images of all the original boundary centers belongs to the
isomorphism locus of the projection from the ordered blowup tower. -/
theorem mem_isoLocus_toBase_alongBoundary (i : D ⟶ X) [IsClosedImmersion i]
    (J : Fin n → {A : D.IdealSheafData // A.IsEffectiveCartier}) {x : X}
    (hx : ∀ j, x ∉ i '' ((J j).val.support : Set D)) :
    x ∈ (alongBoundary i J).2.toTower.toBase.isoLocus := by
  let Z : Set X := ⋃ j, i '' ((J j).val.support : Set D)
  let U : X.Opens := ⟨Zᶜ, (isClosed_iUnion_of_finite
    fun j ↦ i.isClosedEmbedding.isClosedMap _ (J j).val.support.isClosed).isOpen_compl⟩
  refine (alongBoundary i J).2.toTower.toBase.mem_isoLocus_iff.mpr
    ⟨U, by simpa [U, Z] using hx, isIso_toBase_restrict_alongBoundary i J U ?_⟩
  exact fun j ↦ Set.disjoint_left.mpr fun y hy hj ↦ hy (Set.mem_iUnion.mpr ⟨j, hj⟩)

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

/-- An ordered tower pulls back along a morphism that is an isomorphism over the
specified centers. On the reduced inverse image of the original boundary, each
center is pulled back by a cartesian square with identity on the center scheme.
The final strict boundary is the reduced inverse image of the original tower's
strict boundary. -/
theorem exists_isPullback_alongBoundary_radical (D : X.IdealSheafData) [IsReduced D.subscheme]
    (f : X' ⟶ X) {S : Fin n → Scheme.{u}} (a : ∀ j, S j ⟶ D.subscheme)
    [∀ j, IsClosedImmersion (a j)] (hC : ∀ j, (a j).ker.IsEffectiveCartier)
    (hiso : ∀ j, Set.range (a j ≫ D.subschemeι) ⊆ f.isoLocus) :
    let E := (D.comap f).radical
    let d := subschemeMap E D f (le_map_iff_comap_le.mpr (le_radical _))
    ∃ (a' : ∀ j, S j ⟶ E.subscheme) (hC' : ∀ j, (a' j).ker.IsEffectiveCartier),
      (∀ j, IsPullback (a' j) (𝟙 (S j)) d (a j)) ∧
      let A := alongBoundary D.subschemeι (fun j ↦ ⟨(a j).ker, hC j⟩)
      let B := alongBoundary E.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)
      ∃ q : B.1 ⟶ A.1, IsPullback q B.2.toTower.toBase A.2.toTower.toBase f ∧
        B.2.boundaryι ≫ q = d ≫ A.2.boundaryι ∧
        (A.2.boundaryι.ker.comap q).radical = B.2.boundaryι.ker := by
  let E := (D.comap f).radical
  let d := subschemeMap E D f (le_map_iff_comap_le.mpr (le_radical _))
  have hd := D.preimage_isoLocus_le_subschemeMap_radical f
  have hcenter (j : Fin n) : Set.range (a j) ⊆ d.isoLocus := by
    rintro _ ⟨x, rfl⟩
    exact hd (D.subschemeι.mem_preimage.mpr (hiso j ⟨x, Scheme.Hom.comp_apply _ _ _⟩))
  choose a' ha' using fun j ↦ d.exists_isPullback_id_of_range_subset_isoLocus (a j) (hcenter j)
  have ha (j : Fin n) : a' j ≫ d = a j := by simpa only [Category.id_comp] using (ha' j).w
  have hC' (j : Fin n) : (a' j).ker.IsEffectiveCartier := by
    rw [ker_eq_comap_of_isPullback _ (ha' j)]
    apply (hC j).comap_of_support_subset_isoLocus d
    simpa only [(a j).support_ker, (a j).isClosedEmbedding.isClosed_range.closure_eq] using
      hcenter j
  obtain ⟨q, hq, hb⟩ := exists_isPullback_alongBoundary
    (subschemeMap_subschemeι E D f _).symm a a' ha hC hC' hiso
  let A := alongBoundary D.subschemeι (fun j ↦ ⟨(a j).ker, hC j⟩)
  let B := alongBoundary E.subschemeι (fun j ↦ ⟨(a' j).ker, hC' j⟩)
  have : IsClosedImmersion (A.2.boundaryι ≫ A.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have : IsClosedImmersion (B.2.boundaryι ≫ B.2.toTower.toBase) := by
    rw [WithBoundary.boundaryι_toBase]
    infer_instance
  have : IsReduced E.subscheme := by
    dsimp only [E]
    rw [← vanishingIdeal_support (I := D.comap f)]
    infer_instance
  have hbase : (((A.2.boundaryι ≫ A.2.toTower.toBase).ker).comap f).radical =
      (B.2.boundaryι ≫ B.2.toTower.toBase).ker := by
    simp only [WithBoundary.boundaryι_toBase, ker_subschemeι, E]
  exact ⟨a', hC', ha', q, hq, hb,
    radical_comap_ker_eq_of_isPullback hq A.2.boundaryι B.2.boundaryι d hb hbase⟩

end QPainleve.BlowupTower
