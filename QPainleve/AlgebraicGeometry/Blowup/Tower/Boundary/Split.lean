/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary

/-!
# Splitting off the first blowup along a boundary

The tail of an ordered boundary tower can be constructed on the blowup of the first
center, using the lifted embedding of the same boundary. This comparison preserves
the projection to the original scheme and the final embedding of the boundary.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D X : Scheme.{u}} {i : D ⟶ X} [IsClosedImmersion i]

/-- An ordered boundary tower with first center `A` is the tower of its remaining centers
on the blowup of the image of `A`. The comparison is over the original scheme and
identifies the embeddings of the fixed boundary. -/
theorem exists_iso_alongBoundary_cons
    (A : {J : D.IdealSheafData // J.IsEffectiveCartier})
    {I : X.IdealSheafData} (hI : A.val.map i = I)
    (j : D ⟶ I.blowup) [IsClosedImmersion j] (hj : j ≫ I.blowupToBase = i)
    {n : ℕ} (J : Fin n → {K : D.IdealSheafData // K.IsEffectiveCartier}) :
    ∃ e : (alongBoundary i (Fin.cons A J)).1 ≅ (alongBoundary j J).1,
      e.hom ≫ (alongBoundary j J).2.toTower.toBase ≫ I.blowupToBase =
        (alongBoundary i (Fin.cons A J)).2.toTower.toBase ∧
      (alongBoundary i (Fin.cons A J)).2.boundaryι ≫ e.hom = (alongBoundary j J).2.boundaryι := by
  induction n with
  | zero =>
    let T := WithBoundary.nil i
    have heq : I.comap (Iso.refl X).hom = A.val.map T.boundaryι := by
      simpa only [T, WithBoundary.boundaryι_nil, Iso.refl_hom, comap_id] using hI.symm
    let e := I.blowupIso (Iso.refl X) heq
    have he : e.hom ≫ I.blowupToBase = (A.val.map T.boundaryι).blowupToBase := by simp [e]
    have hproj : (T.snoc A.val A.property).boundaryι ≫ e.hom ≫ I.blowupToBase = i := by
      rw [he, WithBoundary.boundaryι_snoc_blowupToBase, WithBoundary.boundaryι_nil]
    rw [alongBoundary_succ i, alongBoundary_zero i, alongBoundary_zero j,
      Fin.last_zero, Fin.cons_zero]
    simp only [WithBoundary.toTower_nil, WithBoundary.toTower_snoc,
      toBase_snoc, toBase_nil, Category.id_comp, Category.comp_id]
    refine ⟨e, he, I.blowup_hom_ext ?_ ?_⟩
    · simpa only [Category.assoc, WithBoundary.boundaryι_nil, hj] using hproj
    · rw [Category.assoc, hproj, ← hI, comap_map_of_isClosedImmersion]
      exact A.property
  | succ n ih =>
    let K := fun k : Fin n ↦ J k.castSucc
    have hprefix : (fun k : Fin (n + 1) ↦
        (Fin.cons A J : Fin (n + 2) → {K : D.IdealSheafData // K.IsEffectiveCartier})
          k.castSucc) = Fin.cons A K := by
      funext k
      refine Fin.cases ?_ (fun l ↦ ?_) k
      · simp
      · simp [K, Fin.castSucc_succ]
    obtain ⟨e, he, hb⟩ := ih K
    rw [alongBoundary_succ i, alongBoundary_succ j, hprefix, Fin.cons_last]
    dsimp only
    let T := (alongBoundary i (Fin.cons A K)).2
    let U := (alongBoundary j K).2
    let B := J (Fin.last n)
    have hb' : T.boundaryι ≫ e.hom = (Iso.refl D).hom ≫ U.boundaryι := by simpa using hb
    have hB : B.val.comap (Iso.refl D).hom = B.val := by simp
    let e' := (B.val.map U.boundaryι).blowupIso e
      (T.comap_center_eq B.val e (Iso.refl D) hb' B.val hB)
    have he' : e'.hom ≫ (B.val.map U.boundaryι).blowupToBase =
        (B.val.map T.boundaryι).blowupToBase ≫ e.hom := blowupIso_hom_blowupToBase _ _ _
    refine ⟨e', ?_, ?_⟩
    · simp only [WithBoundary.toTower_snoc, toBase_snoc]
      calc
        _ = (B.val.map T.boundaryι).blowupToBase ≫ e.hom ≫ U.toTower.toBase ≫
            I.blowupToBase := (reassoc_of% he') _
        _ = _ := congrArg ((B.val.map T.boundaryι).blowupToBase ≫ ·) he
    · simpa only [Iso.refl_hom, Category.id_comp] using
        T.boundaryι_snoc_blowupIso_hom B.val e (Iso.refl D) hb' B.val hB B.property B.property

end QPainleve.BlowupTower
