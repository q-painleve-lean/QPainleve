/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Blowups along a fixed boundary

When the center is an effective Cartier subscheme of the boundary, the strict transform
is canonically the same boundary in the new ambient scheme. This lets us use a fixed
boundary scheme to prescribe ordered centers. In particular, a section through the
smooth locus of a boundary curve can be used repeatedly. Each blowup takes the image of
the section in the current surface.

The Cartier property for smooth sections uses Tau Ceti's
`Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id`.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData (blowupIso)

universe u

namespace QPainleve.BlowupTower

/-- An ordered blowup tower equipped with a closed embedding of a fixed boundary over the original
embedding `i`. -/
@[ext]
structure WithBoundary {D X : Scheme.{u}} (i : D ⟶ X) (n : ℕ) (Y : Scheme.{u}) where
  /-- The underlying ordered tower. -/
  toTower : BlowupTower X n Y
  /-- The embedding of the boundary in the current scheme. -/
  boundaryι : D ⟶ Y
  /-- The boundary is a closed subscheme of the current scheme. -/
  isClosedImmersion_boundaryι : IsClosedImmersion boundaryι
  /-- The current boundary projects back to the original embedding. -/
  boundaryι_toBase : boundaryι ≫ toTower.toBase = i

attribute [instance] WithBoundary.isClosedImmersion_boundaryι
attribute [reassoc (attr := simp)] WithBoundary.boundaryι_toBase

noncomputable section

namespace WithBoundary

variable {D D' X X' Y Y' S : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'} {n : ℕ}

/-- The empty tower with its given boundary. -/
def nil (i : D ⟶ X) [IsClosedImmersion i] : WithBoundary i 0 X where
  toTower := .nil
  boundaryι := i
  isClosedImmersion_boundaryι := inferInstance
  boundaryι_toBase := by simp

@[simp]
theorem toTower_nil (i : D ⟶ X) [IsClosedImmersion i] :
    (nil i).toTower = .nil := (rfl)

@[simp]
theorem boundaryι_nil (i : D ⟶ X) [IsClosedImmersion i] :
    (nil i).boundaryι = i := (rfl)

/-- The total transform of a closed subscheme of the original boundary restricts
to the original ideal on the final boundary. -/
@[simp]
theorem comap_map_toBase_boundaryι [IsClosedImmersion i]
    (T : WithBoundary i n Y) (J : D.IdealSheafData) :
    ((J.map i).comap T.toTower.toBase).comap T.boundaryι = J := by
  rw [← Scheme.IdealSheafData.comap_comp, boundaryι_toBase,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

variable (T : WithBoundary i n Y) (J : D.IdealSheafData)

private theorem isEffectiveCartier_comap_center (hJ : J.IsEffectiveCartier) :
    ((J.map T.boundaryι).comap T.boundaryι).IsEffectiveCartier := by
  simpa using hJ

/-- Append the blowup of the image of a Cartier center on the fixed boundary. The new boundary
embedding represents the scheme-theoretic strict transform. -/
def snoc (hJ : J.IsEffectiveCartier) : WithBoundary i (n + 1) (J.map T.boundaryι).blowup where
  toTower := T.toTower.snoc (J.map T.boundaryι)
  boundaryι := (J.map T.boundaryι).blowupLift T.boundaryι (T.isEffectiveCartier_comap_center J hJ)
  isClosedImmersion_boundaryι := (J.map T.boundaryι).isClosedImmersion_blowupLift _ _
  boundaryι_toBase := by simp

@[simp]
theorem toTower_snoc (hJ : J.IsEffectiveCartier) :
    (T.snoc J hJ).toTower = T.toTower.snoc (J.map T.boundaryι) := (rfl)

/-- The updated boundary is the canonical lift of its previous embedding. -/
theorem boundaryι_snoc (hJ : J.IsEffectiveCartier) :
    (T.snoc J hJ).boundaryι =
      (J.map T.boundaryι).blowupLift T.boundaryι (by simpa using hJ) := (rfl)

/-- The projection of the new boundary is its previous embedding. -/
@[reassoc (attr := simp)]
theorem boundaryι_snoc_blowupToBase (hJ : J.IsEffectiveCartier) :
    (T.snoc J hJ).boundaryι ≫ (J.map T.boundaryι).blowupToBase = T.boundaryι := by
  rw [boundaryι_snoc, Scheme.IdealSheafData.blowupLift_blowupToBase]

/-- The lifted boundary has the ideal of the scheme-theoretic strict transform. -/
@[simp]
theorem ker_boundaryι_snoc (hJ : J.IsEffectiveCartier) :
    (T.snoc J hJ).boundaryι.ker = ((J.map T.boundaryι).blowupMap T.boundaryι).ker := by
  rw [boundaryι_snoc, Scheme.IdealSheafData.ker_blowupLift, Scheme.IdealSheafData.ker_blowupMap]

/-- The exceptional divisor intersects the strict transform of the boundary in the
original center as a closed subscheme of the fixed boundary. -/
@[simp]
theorem comap_exceptional_boundaryι_snoc (hJ : J.IsEffectiveCartier) :
    let I := J.map T.boundaryι
    (I.comap I.blowupToBase).comap (T.snoc J hJ).boundaryι = J := by
  simp [boundaryι_snoc]

/-- Append a blowup at a closed section in the smooth locus of a relative boundary curve.
The center is the kernel of the section composed with the current boundary embedding,
by `Scheme.IdealSheafData.map_ker`. -/
def snocSection (f : D ⟶ S) (s : S ⟶ D) [IsClosedImmersion s] (hs : s ≫ f = 𝟙 S)
    (U : D.Opens) (hU : Set.range s ⊆ U) [SmoothOfRelativeDimension 1 (U.ι ≫ f)] :
    WithBoundary i (n + 1) (s.ker.map T.boundaryι).blowup :=
  T.snoc s.ker (Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id s hs U hU)

/-- A closed section through the smooth locus supplies a Cartier center on the boundary. -/
theorem snocSection_eq_snoc (f : D ⟶ S) (s : S ⟶ D) [IsClosedImmersion s]
    (hs : s ≫ f = 𝟙 S) (U : D.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)] :
    T.snocSection f s hs U hU =
      T.snoc s.ker (Scheme.Hom.isEffectiveCartier_ker_of_comp_eq_id s hs U hU) := (rfl)

/-- Isomorphisms matching the boundary embeddings and Cartier centers also match their
ambient center ideals. -/
theorem comap_center_eq {m : ℕ} {T' : WithBoundary i' m Y'} (g : Y ≅ Y') (d : D ≅ D')
    (hg : T.boundaryι ≫ g.hom = d.hom ≫ T'.boundaryι)
    (J' : D'.IdealSheafData) (hJ : J'.comap d.hom = J) :
    (J'.map T'.boundaryι).comap g.hom = J.map T.boundaryι := by
  have hmap : J.map d.hom = J' := by
    rw [← hJ, Scheme.IdealSheafData.map_comap_of_isClosedImmersion,
      Scheme.Hom.ker_eq_bot_of_isIso, sup_bot_eq]
  rw [← hmap, ← Scheme.IdealSheafData.map_comp, ← hg, Scheme.IdealSheafData.map_comp,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- If two maps into the boundaries are compatible with the ambient isomorphism,
their strict-transform maps remain compatible provided the center pulls back to a
Cartier ideal on the common source. -/
@[reassoc]
theorem comp_boundaryι_snoc_blowupIso_hom {m : ℕ} {T' : WithBoundary i' m Y'} (g : Y ≅ Y')
    (a : S ⟶ D) (a' : S ⟶ D')
    (ha : a ≫ T.boundaryι ≫ g.hom = a' ≫ T'.boundaryι)
    (J' : D'.IdealSheafData) (hJ : (J'.map T'.boundaryι).comap g.hom = J.map T.boundaryι)
    (h : J.IsEffectiveCartier) (h' : J'.IsEffectiveCartier) (hc : (J.comap a).IsEffectiveCartier) :
    a ≫ (T.snoc J h).boundaryι ≫ (blowupIso g hJ.symm).hom =
      a' ≫ (T'.snoc J' h').boundaryι := by
  apply (J'.map T'.boundaryι).blowup_hom_ext
  · simpa only [Category.assoc, Scheme.IdealSheafData.blowupIso_hom_blowupToBase,
      boundaryι_snoc_blowupToBase_assoc, boundaryι_snoc_blowupToBase] using ha
  · simp only [Category.assoc, Scheme.IdealSheafData.blowupIso_hom_blowupToBase,
      boundaryι_snoc_blowupToBase_assoc]
    rw [Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, hJ, Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
    exact hc

/-- The lifted isomorphism of the blowups intertwines the strict-transform boundary
embeddings. -/
@[reassoc]
theorem boundaryι_snoc_blowupIso_hom {m : ℕ} {T' : WithBoundary i' m Y'} (g : Y ≅ Y') (d : D ≅ D')
    (hg : T.boundaryι ≫ g.hom = d.hom ≫ T'.boundaryι)
    (J' : D'.IdealSheafData) (hJ : J'.comap d.hom = J)
    (h : J.IsEffectiveCartier) (h' : J'.IsEffectiveCartier) :
    (T.snoc J h).boundaryι ≫
        (blowupIso g (T.comap_center_eq J g d hg J' hJ).symm).hom =
      d.hom ≫ (T'.snoc J' h').boundaryι := by
  simpa only [Category.id_comp] using
    T.comp_boundaryι_snoc_blowupIso_hom J g (𝟙 D) d.hom
      (by simpa only [Category.id_comp] using hg) J' (T.comap_center_eq J g d hg J' hJ)
      h h' (by simpa only [Scheme.IdealSheafData.comap_id] using h)

end WithBoundary

variable {D D' X X' : Scheme.{u}}

/-- The ordered blowups of a family of Cartier centers on a fixed closed boundary. At each
stage the center is mapped into the current scheme through the latest strict transform.
The input may use the same boundary subscheme at several indices. -/
def alongBoundary (i : D ⟶ X) [IsClosedImmersion i] :
    {n : ℕ} → (Fin n → {J : D.IdealSheafData // J.IsEffectiveCartier}) →
      Σ Y, WithBoundary i n Y
  | 0, _ => ⟨X, .nil i⟩
  | n + 1, J =>
    let T := alongBoundary i (fun j : Fin n ↦ J j.castSucc)
    ⟨_, T.2.snoc (J (Fin.last n)).val (J (Fin.last n)).property⟩

/-- An empty family of centers leaves the boundary and its ambient scheme unchanged. -/
@[simp]
theorem alongBoundary_zero (i : D ⟶ X) [IsClosedImmersion i]
    (J : Fin 0 → {J : D.IdealSheafData // J.IsEffectiveCartier}) :
    alongBoundary i J = ⟨X, .nil i⟩ := (rfl)

/-- To build an ordered boundary tower, append the last blowup to the prefix tower. -/
@[simp]
theorem alongBoundary_succ (i : D ⟶ X) [IsClosedImmersion i] {n : ℕ}
    (J : Fin (n + 1) → {J : D.IdealSheafData // J.IsEffectiveCartier}) :
    alongBoundary i J =
      ⟨_, (alongBoundary i (fun j : Fin n ↦ J j.castSucc)).2.snoc
        (J (Fin.last n)).val (J (Fin.last n)).property⟩ := (rfl)

/-- A map to an ordered boundary blowup with projection factoring through the base
boundary factors through its canonical strict transform by the same map if each center
pulls back to an effective Cartier ideal. -/
theorem eq_comp_boundaryι_of_comp_toBase_eq {S : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] {n : ℕ} (J : Fin n → {K : D.IdealSheafData // K.IsEffectiveCartier})
    (a : S ⟶ D) (ha : ∀ j, ((J j).val.comap a).IsEffectiveCartier)
    (f : S ⟶ (alongBoundary i J).1) (hf : f ≫ (alongBoundary i J).2.toTower.toBase = a ≫ i) :
    f = a ≫ (alongBoundary i J).2.boundaryι := by
  let P {m : ℕ} (U : Σ Y, WithBoundary i m Y) :=
    ∀ f : S ⟶ U.1, f ≫ U.2.toTower.toBase = a ≫ i → f = a ≫ U.2.boundaryι
  suffices P (alongBoundary i J) from this f hf
  clear f hf
  induction n with
  | zero =>
    refine (congrArg P (alongBoundary_zero i J)).mpr ?_
    intro f hf
    simpa only [WithBoundary.toTower_nil, toBase_nil, Category.comp_id,
      WithBoundary.boundaryι_nil] using hf
  | succ n ih =>
    refine (congrArg P (alongBoundary_succ i J)).mpr ?_
    intro f hf
    let T := (alongBoundary i (fun j : Fin n ↦ J j.castSucc)).2
    let K := J (Fin.last n)
    let I := K.val.map T.boundaryι
    have hf' : (f ≫ I.blowupToBase) ≫ T.toTower.toBase = a ≫ i := by
      simpa only [WithBoundary.toTower_snoc, toBase_snoc, Category.assoc] using hf
    have h := ih (fun j ↦ J j.castSucc) (fun j ↦ ha j.castSucc) (f ≫ I.blowupToBase) hf'
    apply I.blowup_hom_ext
    · exact h.trans ((Category.assoc _ _ _).trans
        (congrArg (a ≫ ·) (T.boundaryι_snoc_blowupToBase K.val K.property))).symm
    · exact h.symm ▸ (by
        rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
        exact ha (Fin.last n))

/-- A morphism of boundary blowup towers over the same base intertwines the
two strict boundary embeddings. -/
theorem boundaryι_comp_of_alongBoundary (i : D ⟶ X) [IsClosedImmersion i] {m n : ℕ}
    {J : Fin m → {I : D.IdealSheafData // I.IsEffectiveCartier}}
    {K : Fin n → {I : D.IdealSheafData // I.IsEffectiveCartier}}
    (f : (alongBoundary i J).1 ⟶ (alongBoundary i K).1)
    (hf : f ≫ (alongBoundary i K).2.toTower.toBase = (alongBoundary i J).2.toTower.toBase) :
    (alongBoundary i J).2.boundaryι ≫ f = (alongBoundary i K).2.boundaryι := by
  simpa only [Category.id_comp] using
    eq_comp_boundaryι_of_comp_toBase_eq i K (𝟙 D)
      (fun j ↦ by simpa only [Scheme.IdealSheafData.comap_id] using (K j).property)
      ((alongBoundary i J).2.boundaryι ≫ f)
      (by rw [Category.assoc, hf, WithBoundary.boundaryι_toBase, Category.id_comp])

/-- Isomorphisms matching the original boundary and the ordered centers lift through the
whole tower and match the final strict transforms. Matching the centers is expressed on
their ideal sheaves, so the statement applies also when a center occurs more than once. -/
theorem exists_isLift_alongBoundary {i : D ⟶ X} {i' : D' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] (e : X ≅ X') (d : D ≅ D')
    (hi : i ≫ e.hom = d.hom ≫ i') {n : ℕ}
    (J : Fin n → {J : D.IdealSheafData // J.IsEffectiveCartier})
    (J' : Fin n → {J : D'.IdealSheafData // J.IsEffectiveCartier})
    (hJ : ∀ j, (J' j).val.comap d.hom = (J j).val) :
    ∃ g : (alongBoundary i J).1 ≅ (alongBoundary i' J').1,
      IsLift e (alongBoundary i J).2.toTower (alongBoundary i' J').2.toTower g ∧
        (alongBoundary i J).2.boundaryι ≫ g.hom = d.hom ≫ (alongBoundary i' J').2.boundaryι := by
  induction n with
  | zero => exact ⟨e, IsLift.nil_iff.mpr rfl, hi⟩
  | succ n ih =>
    let T := (alongBoundary i (fun j : Fin n ↦ J j.castSucc)).2
    let T' := (alongBoundary i' (fun j : Fin n ↦ J' j.castSucc)).2
    let C := J (Fin.last n)
    let C' := J' (Fin.last n)
    obtain ⟨g, hg, hb⟩ := ih (fun j ↦ J j.castSucc) (fun j ↦ J' j.castSucc)
      (fun j ↦ hJ j.castSucc)
    have hlast := hJ (Fin.last n)
    have hcenter := T.comap_center_eq C.val g d hb C'.val hlast
    exact ⟨_, hg.snoc hcenter,
      T.boundaryι_snoc_blowupIso_hom C.val g d hb C'.val hlast C.property C'.property⟩

/-- A lift through ordered boundary blowups matches the prescribed centers on the original
boundaries and intertwines the final strict-transform embeddings. -/
theorem IsLift.alongBoundary {i : D ⟶ X} {i' : D' ⟶ X'}
    [IsClosedImmersion i] [IsClosedImmersion i'] {e : X ≅ X'} (d : D ≅ D')
    (hi : i ≫ e.hom = d.hom ≫ i') {n : ℕ}
    {J : Fin n → {J : D.IdealSheafData // J.IsEffectiveCartier}}
    {J' : Fin n → {J : D'.IdealSheafData // J.IsEffectiveCartier}}
    {g : (alongBoundary i J).1 ≅ (alongBoundary i' J').1}
    (hg : IsLift e (alongBoundary i J).2.toTower (alongBoundary i' J').2.toTower g) :
    (∀ j, (J' j).val.comap d.hom = (J j).val) ∧
      (alongBoundary i J).2.boundaryι ≫ g.hom = d.hom ≫ (alongBoundary i' J').2.boundaryι := by
  induction n with
  | zero =>
    rcases IsLift.nil_iff.mp hg with rfl
    exact ⟨fun j ↦ j.elim0, hi⟩
  | succ n ih =>
    let T := (BlowupTower.alongBoundary i (fun j : Fin n ↦ J j.castSucc)).2
    let T' := (BlowupTower.alongBoundary i' (fun j : Fin n ↦ J' j.castSucc)).2
    let C := J (Fin.last n)
    let C' := J' (Fin.last n)
    obtain ⟨f, hf, hcenter, rfl⟩ := IsLift.snoc_iff.mp hg
    obtain ⟨hprefix, hb⟩ := ih hf
    have hlast : C'.val.comap d.hom = C.val := by
      rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion C'.val T'.boundaryι,
        ← Scheme.IdealSheafData.comap_comp, ← hb, Scheme.IdealSheafData.comap_comp,
        hcenter, Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
    exact ⟨Fin.lastCases hlast hprefix,
      T.boundaryι_snoc_blowupIso_hom C.val f d hb C'.val hlast C.property C'.property⟩

end
end QPainleve.BlowupTower
