/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Reorder

/-!
# Reordering the marked toric mutation pivot

Moving the first occurrence of a binomial center to the start of the tower
preserves the full Picard marking when the coordinates are reindexed along
with the centers. This lets the Picard calculation of an elementary
transformation at the first blowup be used in the original label order.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}

/-- Move the first occurrence of a binomial center to the beginning of the marked
toric blowup tower. The other centers keep their relative order, including later
occurrences of the pivot. The isomorphism over the fan scheme sends the strict
boundary to the strict boundary, and its Picard pullback undoes the reindexing
of the exceptional coordinates. -/
theorem exists_iso_internalBlowupTower_move_to_front (hΦ : Φ.IsRegular)
    (b : Module.Basis (Fin 2) ℤ N) (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → ℂˣ)
    (k : Fin (n + 1)) (h : ∀ j < k, (s j, c j) ≠ (s k, c k)) :
    let σ := Fin.cons k k.succAbove
    let A := internalBlowupTower b s c
    let B := internalBlowupTower b (s ∘ σ) (c ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass Φ.algebraicRealization)) (x : Fin (n + 1) → ℤ),
        pullback e.hom (internalBlowupPicardMarking b (s ∘ σ) (c ∘ σ) hΦ (a, x ∘ σ)).toMul =
          (internalBlowupPicardMarking b s c hΦ (a, x)).toMul := by
  let D := Φ.boundaryIdeal inferInstance
  let J (j : Fin (n + 1)) := (s j).internalCenter b (c j)
  have hd (j : Fin (n + 1)) (hj : j < k) :
      Disjoint ((J j).val.support : Set D.subscheme) ((J k).val.support : Set D.subscheme) := by
    simpa only [J, Scheme.IdealSheafData.map_id] using
      (disjoint_support_map_internalCenter_iff b (𝟙 _) (s j) (s k) (c j) (c k)).mpr (h j hj)
  dsimp only
  simp only [internalBlowupPicardMarking_apply]
  -- The type of the isomorphism depends on the two ordered models.
  let P (A B : Σ Y, WithBoundary D.subschemeι (n + 1) Y) : Prop :=
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass Φ.algebraicRealization)) (x : Fin (n + 1) → ℤ),
        pullback e.hom (B.2.toTower.picardHom (a, x ∘ Fin.cons k k.succAbove)).toMul =
          (A.2.toTower.picardHom (a, x)).toMul
  change P (internalBlowupTower b s c)
    (internalBlowupTower b (s ∘ Fin.cons k k.succAbove) (c ∘ Fin.cons k k.succAbove))
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  exact exists_iso_alongBoundary_move_to_front (i := D.subschemeι) J k hd

end TauCeti.Toric.Fan
