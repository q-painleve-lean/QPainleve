/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import QPainleve.Geometry.Toric.Fan.Boundary.InternalCenter
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic

import Mathlib.Data.List.FinRange
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Reorder
import QPainleve.Geometry.Toric.Fan.Smooth

/-!
# Ordered internal blowups of a toric surface

An oriented rank-two fan and an ordered list of rays with nonzero center parameters determine
an actual tower of point blowups. Each center is placed on the current strict transform of the
reduced toric boundary. The same ray and parameter can occur repeatedly, giving centers that
are infinitely near. Reordering the centers preserves the model over its original fan scheme.
The Picard marking uses full transforms of the exceptional classes.

The models follow Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Definition 1.2. The construction uses `Ray.binomialCenterOnBoundary` and
`QPainleve.BlowupTower.alongBoundary`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

section BinomialCenters

variable [Nonempty Φ.cones] {n : ℕ} (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → ℂˣ)
  (J : Fin n →
    {K : (Φ.boundaryIdeal inferInstance).subscheme.IdealSheafData // K.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)).ker)

include hJ in
/-- An ordered family of binomial centers gives a tower of reduced closed point blowups. -/
theorem isClosedPointTower_alongBoundary_binomialCenters :
    IsClosedPointTower Φ.algebraicRealization
      (alongBoundary (Φ.boundaryIdeal inferInstance).subschemeι J).2.toTower := by
  apply isClosedPointTower_alongBoundary
  intro j
  rw [hJ j]
  exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary hdim (hm j) (hprim j) (c j)

end BinomialCenters

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.boundaryIdeal h₀
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

variable {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

/-- The ordered internal blowups with the indicated boundary rays and parameters.
At each stage the center is the image of the original binomial point in the current boundary. -/
def internalBlowupTower : Σ Y, WithBoundary (boundary).subschemeι n Y :=
  alongBoundary (boundary).subschemeι fun j ↦ (s j).internalCenter b (c j)

/-- The ordered model uses the determinant-character center ideals in the boundary tower. -/
theorem internalBlowupTower_eq_alongBoundary :
    internalBlowupTower b s c =
      alongBoundary (boundary).subschemeι (fun j ↦ (s j).internalCenter b (c j)) := (rfl)

/-- Reversing the ordered basis and inverting the center parameters gives the same
ordered tower with strict boundary. In particular the equality retains the order of
infinitely near centers. -/
@[simp]
theorem internalBlowupTower_reindex_swap :
    internalBlowupTower (b.reindex (Equiv.swap 0 1)) s c⁻¹ =
      internalBlowupTower b s c := by
  simp [internalBlowupTower_eq_alongBoundary]

/-- The empty list of internal centers leaves the toric model unchanged. -/
@[simp]
theorem internalBlowupTower_zero (s : Fin 0 → Φ.Ray) (c : Fin 0 → ℂˣ) :
    internalBlowupTower b s c = ⟨Φ.algebraicRealization, .nil (boundary).subschemeι⟩ :=
  alongBoundary_zero _ _

/-- The last center is mapped into the model already blown up at the preceding centers. -/
@[simp]
theorem internalBlowupTower_succ (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → ℂˣ) :
    internalBlowupTower b s c =
      let P := internalBlowupTower b (s ∘ Fin.castSucc) (c ∘ Fin.castSucc)
      let J := (s (Fin.last n)).internalCenter b (c (Fin.last n))
      ⟨_, P.2.snoc J.val J.property⟩ :=
  alongBoundary_succ _ _

/-- Reordering the same toric centers gives an isomorphism over the original fan scheme
which identifies the strict boundaries. A repeated ray and parameter still specifies the
same ordered chain of blowups above that point. -/
theorem exists_iso_internalBlowupTower_reindex (σ : Equiv.Perm (Fin n)) :
    let A := internalBlowupTower b s c
    let B := internalBlowupTower b (s ∘ σ) (c ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧ A.2.boundaryι ≫ e.hom = B.2.boundaryι := by
  let J (j : Fin n) := (s j).internalCenter b (c j)
  have hd (a b' : Fin n) (hne : J a ≠ J b') :
      Disjoint ((J a).val.support : Set (boundary).subscheme) ((J b').val.support : Set _) := by
    have hpair : (s a, c a) ≠ (s b', c b') := by
      intro h
      apply hne
      exact congrArg (fun p : Φ.Ray × ℂˣ ↦ p.1.internalCenter b p.2) h
    simpa only [Scheme.IdealSheafData.map_id] using
      (disjoint_support_map_internalCenter_iff b (𝟙 _) (s a) (s b') (c a) (c b')).mpr hpair
  dsimp only
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  exact exists_iso_alongBoundary_perm_of_disjoint J (J ∘ σ) (σ.ofFn_comp_perm J).symm hd

/-- All internal centers are reduced closed points of their successive ambient surfaces. -/
theorem isClosedPointTower_internalBlowupTower :
    IsClosedPointTower Φ.algebraicRealization (internalBlowupTower b s c).2.toTower := by
  rw [internalBlowupTower_eq_alongBoundary]
  exact isClosedPointTower_alongBoundary_binomialCenters rankTwo s
    (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
    (fun j ↦ b.detDualEquiv_self (s j).primitiveGenerator)
    (fun j ↦ (s j).surjective_detCharacter b) c _ (fun j ↦ (s j).internalCenter_val b (c j))

/-- The projection of the ordered internal blowups of a regular toric surface
is a modification. -/
theorem isModification_internalBlowupTower_toBase (hΦ : Φ.IsRegular) :
    IsModification (internalBlowupTower b s c).2.toTower.toBase := by
  have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact
    (isClosedPointTower_internalBlowupTower b s c).isModification_of_smoothOfRelativeDimension_two
      Φ.algebraicRealizationStructureMap

/-- The Picard group of the model is marked by the original toric classes and the full
transforms of the exceptional classes, with coordinates in the given center order. -/
def internalBlowupPicardMarking (hΦ : Φ.IsRegular) :
    (Pic(Φ.algebraicRealization) × (Fin n → ℤ)) ≃ₗ[ℤ]
      Pic((internalBlowupTower b s c).1) := by
  have : SmoothOfRelativeDimension 2 Φ.algebraicRealizationStructureMap :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact (internalBlowupTower b s c).2.toTower.picardMarking
    (isClosedPointTower_internalBlowupTower b s c) Φ.algebraicRealizationStructureMap

/-- The marking pulls back the toric class and adds the indicated total exceptional classes. -/
@[simp]
theorem internalBlowupPicardMarking_apply (hΦ : Φ.IsRegular)
    (a : Pic(Φ.algebraicRealization) × (Fin n → ℤ)) :
    internalBlowupPicardMarking b s c hΦ a = (internalBlowupTower b s c).2.toTower.picardHom a := by
  simp [internalBlowupPicardMarking]

open LineBundleClass in
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
