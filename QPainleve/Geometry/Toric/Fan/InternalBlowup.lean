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
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Split
import QPainleve.Geometry.Toric.BaseChange.FiniteType

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

universe u

variable (K : Type u) [Field K] {N : Type u} {V : Type*}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

section BinomialCenters

variable [Nonempty Φ.cones] {n : ℕ} (hdim : Module.finrank ℤ N = 2)
  (s : Fin n → Φ.Ray) (m : Fin n → N →+ ℤ)
  (hm : ∀ j, m j (s j).primitiveGenerator = 0) (hprim : ∀ j, Function.Surjective (m j))
  (c : Fin n → Kˣ)
  (J : Fin n →
    {I : (Φ.toricBoundaryIdeal K inferInstance).subscheme.IdealSheafData // I.IsEffectiveCartier})
  (hJ : ∀ j, (J j).val = ((s j).binomialCenterOnBoundary K hdim (hm j) (hprim j) (c j)).ker)

include hJ in
/-- An ordered family of binomial centers gives a tower of reduced closed point blowups. -/
theorem isClosedPointTower_alongBoundary_binomialCenters :
    IsClosedPointTower (Φ.finiteFanScheme K)
      (alongBoundary (Φ.toricBoundaryIdeal K inferInstance).subschemeι J).2.toTower := by
  apply isClosedPointTower_alongBoundary
  intro j
  rw [hJ j]
  exact (s j).exists_closedPoint_ker_binomialCenterOnBoundary K hdim (hm j) (hprim j) (c j)

end BinomialCenters

variable [h₀ : Nonempty Φ.cones] (b : Module.Basis (Fin 2) ℤ N)

local notation "boundary" => Φ.toricBoundaryIdeal K h₀
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))

variable {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → Kˣ)

/-- The ordered internal blowups with the indicated boundary rays and parameters.
At each stage the center is the image of the original binomial point in the current boundary. -/
def internalBlowupTower : Σ Y, WithBoundary (boundary).subschemeι n Y :=
  alongBoundary (boundary).subschemeι fun j ↦ (s j).internalCenter K b (c j)

/-- The ordered model uses the determinant-character center ideals in the boundary tower. -/
theorem internalBlowupTower_eq_alongBoundary :
    internalBlowupTower K b s c =
      alongBoundary (boundary).subschemeι (fun j ↦ (s j).internalCenter K b (c j)) := (rfl)

/-- Reversing the ordered basis and inverting the center parameters gives the same
ordered tower with strict boundary. In particular the equality retains the order of
infinitely near centers. -/
@[simp]
theorem internalBlowupTower_reindex_swap :
    internalBlowupTower K (b.reindex (Equiv.swap 0 1)) s c⁻¹ =
      internalBlowupTower K b s c := by
  simp [internalBlowupTower_eq_alongBoundary]

/-- In any lattice basis the same ordered tower is obtained by reparametrizing its
individual centers. Equality retains the intermediate blowups and the strict boundary. -/
theorem exists_internalBlowupTower_eq_of_basis (d : Module.Basis (Fin 2) ℤ N) :
    ∃ a : Fin n → Kˣ, internalBlowupTower K d s a = internalBlowupTower K b s c := by
  choose a ha using fun j ↦ (s j).exists_internalCenter_eq_of_basis K d b (c j)
  exact ⟨a, congrArg (alongBoundary (boundary).subschemeι) (funext ha)⟩

/-- The empty list of internal centers leaves the toric model unchanged. -/
@[simp]
theorem internalBlowupTower_zero (s : Fin 0 → Φ.Ray) (c : Fin 0 → Kˣ) :
    internalBlowupTower K b s c = ⟨(Φ.finiteFanScheme K), .nil (boundary).subschemeι⟩ :=
  alongBoundary_zero _ _

/-- The last center is mapped into the model already blown up at the preceding centers. -/
@[simp]
theorem internalBlowupTower_succ (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → Kˣ) :
    internalBlowupTower K b s c =
      let P := internalBlowupTower K b (s ∘ Fin.castSucc) (c ∘ Fin.castSucc)
      let J := (s (Fin.last n)).internalCenter K b (c (Fin.last n))
      ⟨_, P.2.snoc J.val J.property⟩ :=
  alongBoundary_succ _ _

/-- Reordering the same toric centers gives an isomorphism over the original fan scheme
which identifies the strict boundaries. A repeated ray and parameter still specifies the
same ordered chain of blowups above that point. -/
theorem exists_iso_internalBlowupTower_reindex (σ : Equiv.Perm (Fin n)) :
    let A := internalBlowupTower K b s c
    let B := internalBlowupTower K b (s ∘ σ) (c ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧ A.2.boundaryι ≫ e.hom = B.2.boundaryι := by
  let J (j : Fin n) := (s j).internalCenter K b (c j)
  have hd (a b' : Fin n) (hne : J a ≠ J b') :
      Disjoint ((J a).val.support : Set (boundary).subscheme) ((J b').val.support : Set _) := by
    have hpair : (s a, c a) ≠ (s b', c b') := by
      intro h
      apply hne
      exact congrArg (fun p : Φ.Ray × Kˣ ↦ p.1.internalCenter K b p.2) h
    simpa only [Scheme.IdealSheafData.map_id] using
      (disjoint_support_map_internalCenter_iff K b (𝟙 _) (s a) (s b') (c a) (c b')).mpr hpair
  dsimp only
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  exact exists_iso_alongBoundary_perm_of_disjoint J (J ∘ σ) (σ.ofFn_comp_perm J).symm hd

/-- All internal centers are reduced closed points of their successive ambient surfaces. -/
theorem isClosedPointTower_internalBlowupTower :
    IsClosedPointTower (Φ.finiteFanScheme K) (internalBlowupTower K b s c).2.toTower := by
  rw [internalBlowupTower_eq_alongBoundary]
  exact isClosedPointTower_alongBoundary_binomialCenters K rankTwo s
    (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
    (fun j ↦ b.detDualEquiv_self (s j).primitiveGenerator)
    (fun j ↦ (s j).surjective_detCharacter b) c _ (fun j ↦ (s j).internalCenter_val K b (c j))

/-- Ordered internal blowups of a regular toric surface form a smooth surface. -/
theorem smoothOfRelativeDimension_internalBlowupTower [PerfectField K] (hΦ : Φ.IsRegular) :
    SmoothOfRelativeDimension 2 ((internalBlowupTower K b s c).2.toTower.toBase ≫
      (Φ.finiteFanSchemeToSpec K)) := by
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  exact (isClosedPointTower_internalBlowupTower K b s c).smoothOfRelativeDimension
    (Φ.finiteFanSchemeToSpec K)

/-- The ordered internal blowup model of a regular toric surface is integral. -/
theorem isIntegral_internalBlowupTower [PerfectField K] (hΦ : Φ.IsRegular) :
    IsIntegral (internalBlowupTower K b s c).1 := by
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  exact (isClosedPointTower_internalBlowupTower K b s c).isIntegral
    (Φ.finiteFanSchemeToSpec K)

/-- The projection of the ordered internal blowups of a regular toric surface
is a modification. -/
theorem isModification_internalBlowupTower_toBase (hΦ : Φ.IsRegular) :
    IsModification (internalBlowupTower K b s c).2.toTower.toBase := by
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  exact
    (isClosedPointTower_internalBlowupTower K b s c).isModification_of_smoothOfRelativeDimension_two
      (Φ.finiteFanSchemeToSpec K)

/-- The Picard group of the model is marked by the original toric classes and the full
transforms of the exceptional classes, with coordinates in the given center order. -/
def internalBlowupPicardMarking [PerfectField K] (hΦ : Φ.IsRegular) :
    (Pic((Φ.finiteFanScheme K)) × (Fin n → ℤ)) ≃ₗ[ℤ]
      Pic((internalBlowupTower K b s c).1) := by
  have : SmoothOfRelativeDimension 2 (Φ.finiteFanSchemeToSpec K) :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec K hΦ
  exact (internalBlowupTower K b s c).2.toTower.picardMarking
    (isClosedPointTower_internalBlowupTower K b s c) (Φ.finiteFanSchemeToSpec K)

/-- The marking pulls back the toric class and adds the indicated total exceptional classes. -/
@[simp]
theorem internalBlowupPicardMarking_apply [PerfectField K] (hΦ : Φ.IsRegular)
    (a : Pic((Φ.finiteFanScheme K)) × (Fin n → ℤ)) :
    internalBlowupPicardMarking K b s c hΦ a =
      (internalBlowupTower K b s c).2.toTower.picardHom a := by
  simp [internalBlowupPicardMarking]

open LineBundleClass in
/-- Identifying the blowup models for opposite orientations sends the strict
boundary identically to itself, preserves the projection to the fan, and pulls
back every marked Picard class to the class with the same coordinates. -/
theorem internalBlowupTower_reindex_swap_iso [PerfectField K]
    {l : N →+ V} {Φ : Fan l} [h₀ : Nonempty Φ.cones]
    (b : Module.Basis (Fin 2) ℤ N) {n : ℕ} (s : Fin n → Φ.Ray) (c : Fin n → Kˣ)
    (hΦ : Φ.IsRegular) :
    let A := internalBlowupTower K b s c
    let B := internalBlowupTower K (b.reindex (Equiv.swap 0 1)) s c⁻¹
    let e := eqToIso (congrArg Sigma.fst (internalBlowupTower_reindex_swap K b s c).symm)
    e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ a, pullback e.hom
        (internalBlowupPicardMarking K (b.reindex (Equiv.swap 0 1)) s c⁻¹ hΦ a).toMul =
          (internalBlowupPicardMarking K b s c hΦ a).toMul := by
  dsimp only
  simp only [internalBlowupPicardMarking_apply]
  have compare (A B : Σ Y, WithBoundary (Φ.toricBoundaryIdeal K h₀).subschemeι n Y) (h : A = B) :
      let e := eqToIso (congrArg Sigma.fst h)
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
        A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
        ∀ a, pullback e.hom (B.2.toTower.picardHom a).toMul =
          (A.2.toTower.picardHom a).toMul := by
    subst B
    simp
  exact compare _ _ (internalBlowupTower_reindex_swap K b s c).symm

open LineBundleClass in
/-- Move the first occurrence of a binomial center to the beginning of the marked
toric blowup tower. The other centers keep their relative order, including later
occurrences of the pivot. The isomorphism over the fan scheme sends the strict
boundary to the strict boundary, and its Picard pullback undoes the reindexing
of the exceptional coordinates. -/
theorem exists_iso_internalBlowupTower_move_to_front
    (b : Module.Basis (Fin 2) ℤ N) (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → Kˣ)
    (k : Fin (n + 1)) (h : ∀ j < k, (s j, c j) ≠ (s k, c k)) :
    let σ := Fin.cons k k.succAbove
    let A := internalBlowupTower K b s c
    let B := internalBlowupTower K b (s ∘ σ) (c ∘ σ)
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass (Φ.finiteFanScheme K))) (x : Fin (n + 1) → ℤ),
        pullback e.hom (B.2.toTower.picardHom (a, x ∘ σ)).toMul =
          (A.2.toTower.picardHom (a, x)).toMul := by
  let D := Φ.toricBoundaryIdeal K inferInstance
  let J (j : Fin (n + 1)) := (s j).internalCenter K b (c j)
  have hd (j : Fin (n + 1)) (hj : j < k) :
      Disjoint ((J j).val.support : Set D.subscheme) ((J k).val.support : Set D.subscheme) := by
    simpa only [J, Scheme.IdealSheafData.map_id] using
      (disjoint_support_map_internalCenter_iff K b (𝟙 _) (s j) (s k) (c j) (c k)).mpr (h j hj)
  dsimp only
  -- The type of the isomorphism depends on the two ordered models.
  let P (A B : Σ Y, WithBoundary D.subschemeι (n + 1) Y) : Prop :=
    ∃ e : A.1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase = A.2.toTower.toBase ∧
      A.2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass (Φ.finiteFanScheme K))) (x : Fin (n + 1) → ℤ),
        pullback e.hom (B.2.toTower.picardHom (a, x ∘ Fin.cons k k.succAbove)).toMul =
          (A.2.toTower.picardHom (a, x)).toMul
  change P (internalBlowupTower K b s c)
    (internalBlowupTower K b (s ∘ Fin.cons k k.succAbove) (c ∘ Fin.cons k k.succAbove))
  rw [internalBlowupTower_eq_alongBoundary, internalBlowupTower_eq_alongBoundary]
  exact exists_iso_alongBoundary_move_to_front (i := D.subschemeι) J k hd

section Split

variable {n : ℕ} (s : Fin (n + 1) → Φ.Ray) (c : Fin (n + 1) → Kˣ)

local notation "A" => internalBlowupTower K b s c

open Scheme.IdealSheafData LineBundleClass in
/-- Split off the first occurrence of a chosen binomial center. The remaining tower
is on its blowup, in the relative order inherited from the original labels.
The comparison preserves the projection and the full Picard marking. -/
theorem exists_iso_internalBlowupTower_split_at
    (k : Fin n.succ) (h : ∀ j < k, (s j, c j) ≠ (s k, c k))
    {I : (Φ.finiteFanScheme K).IdealSheafData}
    (hI : ((s k).internalCenter K b (c k)).val.map (boundary).subschemeι = I)
    {j : (boundary).subscheme ⟶ I.blowup} [IsClosedImmersion j]
    (hj : j ≫ I.blowupToBase = (boundary).subschemeι) :
    let B := alongBoundary j (fun l ↦ (s (k.succAbove l)).internalCenter K b (c (k.succAbove l)))
    ∃ e : (A).1 ≅ B.1,
      e.hom ≫ B.2.toTower.toBase ≫ I.blowupToBase = (A).2.toTower.toBase ∧
      (A).2.boundaryι ≫ e.hom = B.2.boundaryι ∧
      ∀ (a : Additive (LineBundleClass (Φ.finiteFanScheme K))) (x : Fin (n + 1) → ℤ),
        pullback e.hom (B.2.toTower.picardHom
          ((nil.snoc I).picardHom (a, fun _ ↦ x k), x ∘ k.succAbove)).toMul =
          ((A).2.toTower.picardHom (a, x)).toMul := by
  let σ := Fin.cons (α := fun _ ↦ Fin (n + 1)) k k.succAbove
  let J := fun l ↦ (s (k.succAbove l)).internalCenter K b (c (k.succAbove l))
  let J₀ := (s k).internalCenter K b (c k)
  have hmodel : internalBlowupTower K b (s ∘ σ) (c ∘ σ) =
      alongBoundary (boundary).subschemeι (Fin.cons J₀ J) := by
    rw [internalBlowupTower_eq_alongBoundary]
    exact congrArg (alongBoundary (boundary).subschemeι)
      (Fin.comp_cons (fun l ↦ (s l).internalCenter K b (c l)) k k.succAbove)
  have hmove := exists_iso_internalBlowupTower_move_to_front K b s c k h
  dsimp only at hmove
  rw [hmodel] at hmove
  obtain ⟨e, he, heb, hep⟩ := hmove
  obtain ⟨f, hf, hfb, hfp⟩ := exists_iso_alongBoundary_cons J₀ hI j hj J
  refine ⟨e ≪≫ f, ?_, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hf, he]
  · simpa only [Iso.trans_hom, ← Category.assoc, heb] using hfb
  · intro a x
    rw [Iso.trans_hom, ← pullback_comp, hfp, ← Fin.comp_cons, hep]

end Split

end TauCeti.Toric.Fan
