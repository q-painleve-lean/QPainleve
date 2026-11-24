/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
import QPainleve.AlgebraicGeometry.IdealSheaf.CartierPointProduct
import QPainleve.Combinatorics.OrderedFiber
import Mathlib.Algebra.BigOperators.Fin

/-!
# Recovering the centers of an ordered boundary blowup

The ramification ideal of the whole projection restricts to the product of the
original center ideals on the strict boundary. An isomorphism over the base thus
identifies the projected centers with multiplicity and respects the order of
successive blowups above each repeated center.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [hSmooth : SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "Center" => {J : D.IdealSheafData // J.IsEffectiveCartier}

/-- Pulling the ramification ideal of a boundary tower back to the strict boundary
gives one factor for each prescribed center, including repetitions. -/
theorem comap_ramificationIdealSheafToBase_alongBoundary {n : ℕ} (J : Fin n → Center)
    (hT : IsClosedPointTower X (alongBoundary i J).2.toTower) :
    (hT.ramificationIdealSheafToBase k).comap (alongBoundary i J).2.boundaryι =
      ∏ j, (J j).val := by
  induction n with
  | zero =>
    revert hT
    rw [alongBoundary_zero i J]
    intro hT
    simp
  | succ n ih =>
    revert hT
    rw [alongBoundary_succ i J]
    let P := (alongBoundary i fun j : Fin n ↦ J j.castSucc).2
    let K := J (Fin.last n)
    intro hT
    simp only [WithBoundary.toTower_snoc] at hT ⊢
    rw [IsClosedPointTower.ramificationIdealSheafToBase_snoc k hT, comap_mul,
      P.comap_exceptional_boundaryι_snoc K.val K.property, ← comap_comp,
      P.boundaryι_snoc_blowupToBase, ih, Fin.prod_univ_castSucc, mul_comm]

/-- A morphism of boundary blowup towers over the same base intertwines the
two strict boundary embeddings. -/
theorem boundaryι_comp_of_alongBoundary {m n : ℕ} {J : Fin m → Center}
    {K : Fin n → Center} (f : (alongBoundary i J).1 ⟶ (alongBoundary i K).1)
    (hf : f ≫ (alongBoundary i K).2.toTower.toBase = (alongBoundary i J).2.toTower.toBase) :
    (alongBoundary i J).2.boundaryι ≫ f = (alongBoundary i K).2.boundaryι := by
  simpa only [Category.id_comp] using
    eq_comp_boundaryι_of_comp_toBase_eq i K (𝟙 D)
      (fun j ↦ by simpa only [comap_id] using (K j).property)
      ((alongBoundary i J).2.boundaryι ≫ f)
      (by rw [Category.assoc, hf, WithBoundary.boundaryι_toBase, Category.id_comp])

include hSmooth in
/-- Two ordered towers of closed boundary points with isomorphic projections to
the same smooth surface have the same center multiplicities. The matched labels
occur in the same order over each original point. -/
theorem exists_ordered_equiv_of_alongBoundary_iso {m n : ℕ}
    {J : Fin m → Center} {K : Fin n → Center} {p : Fin m → D} {q : Fin n → D}
    (hp : ∀ j, IsClosed ({p j} : Set D)) (hq : ∀ j, IsClosed ({q j} : Set D))
    (hJ : ∀ j, (J j).val = (D.fromSpecResidueField (p j)).ker)
    (hK : ∀ j, (K j).val = (D.fromSpecResidueField (q j)).ker)
    (e : (alongBoundary i J).1 ≅ (alongBoundary i K).1)
    (he : e.hom ≫ (alongBoundary i K).2.toTower.toBase = (alongBoundary i J).2.toTower.toBase) :
    ∃ σ : Fin m ≃ Fin n, (∀ j, q (σ j) = p j) ∧
      ∀ a b, a < b → p a = p b → σ a < σ b := by
  let A := alongBoundary i J
  let B := alongBoundary i K
  let hA := isClosedPointTower_alongBoundary i J fun j ↦ ⟨_, hp j, hJ j⟩
  let hB := isClosedPointTower_alongBoundary i K fun j ↦ ⟨_, hq j, hK j⟩
  let : A.1.Over (Spec (.of k)) := ⟨A.2.toTower.toBase ≫ X ↘ Spec (.of k)⟩
  let : A.2.toTower.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (A.1 ↘ Spec (.of k)) :=
    hA.smoothOfRelativeDimension (X ↘ Spec (.of k))
  have hram : (hB.ramificationIdealSheafToBase k).comap e.hom =
      hA.ramificationIdealSheafToBase k :=
    (hB.comap_ramificationIdealSheafToBase k e he).trans
      (hA.ramificationIdealSheafToBase_def k).symm
  have hprod := congrArg (fun I : A.1.IdealSheafData ↦ I.comap A.2.boundaryι) hram
  rw [← comap_comp, boundaryι_comp_of_alongBoundary i e.hom he,
    comap_ramificationIdealSheafToBase_alongBoundary,
    comap_ramificationIdealSheafToBase_alongBoundary] at hprod
  apply List.Perm.exists_ordered_equiv_ofFn
  apply D.perm_of_prod_ker_fromSpecResidueField_eq
  · simpa only [List.mem_ofFn] using fun x ⟨j, hj⟩ ↦ hj ▸ hp j
  · simpa only [List.mem_ofFn] using fun x ⟨j, hj⟩ ↦ hj ▸ hq j
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hJ j ▸ (J j).property
  · simpa only [List.map_ofFn, Function.comp_apply, List.prod_ofFn, ← hJ, ← hK] using hprod.symm

end QPainleve.BlowupTower
