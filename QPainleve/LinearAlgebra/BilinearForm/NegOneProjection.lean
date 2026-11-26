/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection

/-!
# Successive elimination along vectors of square −1

Blowing down a boundary component of class c and square −1 replaces each surviving class x
by the pullback x + B(x,c)c. To iterate this calculation one uses the updated class of the
next component. The updated contracted classes are pairwise orthogonal and span the same
submodule as their original classes. The composite elimination is Mathlib's
`Submodule.projection` onto the orthogonal complement of that span.
-/

public section

open LinearMap (BilinForm)
open Submodule

namespace LinearMap.BilinForm

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (B : BilinForm R M)

/-- The update x ↦ x + B(x,c)c, which projects off c when B(c,c) = −1. -/
def projectOffNegOne (c : M) : M →ₗ[R] M :=
  LinearMap.id + (LinearMap.toSpanSingleton R M c).comp (B.flip c)

@[simp]
theorem projectOffNegOne_apply (c x : M) :
    B.projectOffNegOne c x = x + B x c • c := (rfl)

/-- The list of vectors at their turn in successive elimination. The head is used to update
the tail before processing the tail. -/
def orthogonalizeNegOnes (B : BilinForm R M) : List M → List M
  | [] => []
  | c :: l => c :: orthogonalizeNegOnes B (l.map (B.projectOffNegOne c))
termination_by l => l.length

@[simp]
theorem orthogonalizeNegOnes_nil : B.orthogonalizeNegOnes [] = [] := by
  rw [orthogonalizeNegOnes]

@[simp]
theorem orthogonalizeNegOnes_cons (c : M) (l : List M) :
    B.orthogonalizeNegOnes (c :: l) =
      c :: B.orthogonalizeNegOnes (l.map (B.projectOffNegOne c)) := by
  rw [orthogonalizeNegOnes]

/-- The linear map obtained by successively eliminating the vectors of a list, updating the
remaining vectors at each step. -/
def projectOffNegOnes (B : BilinForm R M) : List M → M →ₗ[R] M
  | [] => LinearMap.id
  | c :: l => (projectOffNegOnes B (l.map (B.projectOffNegOne c))).comp (B.projectOffNegOne c)
termination_by l => l.length

@[simp]
theorem projectOffNegOnes_nil : B.projectOffNegOnes [] = LinearMap.id := by
  rw [projectOffNegOnes]

@[simp]
theorem projectOffNegOnes_cons (c : M) (l : List M) :
    B.projectOffNegOnes (c :: l) =
      (B.projectOffNegOnes (l.map (B.projectOffNegOne c))).comp (B.projectOffNegOne c) := by
  rw [projectOffNegOnes]

/-- There is one updated class for each entry in the input list. -/
@[simp]
theorem length_orthogonalizeNegOnes (l : List M) :
    (B.orthogonalizeNegOnes l).length = l.length := by
  cases l with
  | nil => simp
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.length_cons,
      length_orthogonalizeNegOnes (l.map (B.projectOffNegOne c)), List.length_map]
termination_by l.length

private theorem projectOffNegOne_sub_mem {P : Submodule R M} {c : M} (hc : c ∈ P) (x : M) :
    B.projectOffNegOne c x - x ∈ P := by
  simpa only [projectOffNegOne_apply, add_sub_cancel_left] using P.smul_mem (B x c) hc

private theorem span_cons_map_projectOffNegOne (c : M) (l : List M) :
    span R {x | x ∈ c :: l.map (B.projectOffNegOne c)} = span R {x | x ∈ c :: l} := by
  apply le_antisymm <;> apply span_le.mpr
  · intro x hx
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact subset_span (List.mem_cons_self ..)
    · rw [projectOffNegOne_apply]
      exact add_mem (subset_span (List.mem_cons_of_mem _ hy))
        (smul_mem _ _ (subset_span (List.mem_cons_self ..)))
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact subset_span (List.mem_cons_self ..)
    · have hproj : B.projectOffNegOne c x ∈ span R {y | y ∈ c :: l.map (B.projectOffNegOne c)} :=
        subset_span (List.mem_cons_of_mem _ (List.mem_map_of_mem hx))
      have hdiff := B.projectOffNegOne_sub_mem
        (P := span R {y | y ∈ c :: l.map (B.projectOffNegOne c)})
        (subset_span (List.mem_cons_self ..)) x
      simpa only [SetLike.mem_coe, sub_sub_cancel] using sub_mem hproj hdiff

/-- The updated classes span the same submodule as the original classes. -/
theorem span_orthogonalizeNegOnes (l : List M) :
    span R {x | x ∈ B.orthogonalizeNegOnes l} = span R {x | x ∈ l} := by
  cases l with
  | nil => simp
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
      span_union, span_orthogonalizeNegOnes (l.map (B.projectOffNegOne c))]
    simpa only [List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton, span_union] using
      B.span_cons_map_projectOffNegOne c l
termination_by l.length

private theorem sub_projectOffNegOnes_mem_span (l : List M) (x : M) :
    x - B.projectOffNegOnes l x ∈ span R {y | y ∈ l} := by
  cases l with
  | nil => simp
  | cons c l =>
    have h₁ : x - B.projectOffNegOne c x ∈ span R {y | y ∈ c :: l} := by
      rw [← neg_sub]
      exact neg_mem (B.projectOffNegOne_sub_mem (subset_span (List.mem_cons_self ..)) x)
    have h₂ := sub_projectOffNegOnes_mem_span (l.map (B.projectOffNegOne c))
      (B.projectOffNegOne c x)
    have hle : span R {y | y ∈ l.map (B.projectOffNegOne c)} ≤ span R {y | y ∈ c :: l} := by
      rw [← B.span_cons_map_projectOffNegOne c l]
      exact span_mono (fun _ hy ↦ List.mem_cons_of_mem _ hy)
    simpa only [sub_add_sub_cancel, projectOffNegOnes_cons, LinearMap.comp_apply] using
      add_mem h₁ (hle h₂)
termination_by l.length

private theorem apply_projectOffNegOne_eq_zero {c : M} (hc : B c c = -1) (x : M) :
    B (B.projectOffNegOne c x) c = 0 := by
  simp [hc]

private theorem span_map_projectOffNegOne_le_ker (c : M) (l : List M) (hc : B c c = -1) :
    span R {x | x ∈ l.map (B.projectOffNegOne c)} ≤ LinearMap.ker (B.flip c) := by
  apply span_le.mpr
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact B.apply_projectOffNegOne_eq_zero hc y

/-- If the vector used at each step has square −1, the updated vectors are pairwise
orthogonal. -/
theorem pairwise_orthogonalizeNegOnes (hB : B.IsRefl) (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) :
    (B.orthogonalizeNegOnes l).Pairwise (fun x y ↦ B x y = 0) := by
  cases l with
  | nil => simp
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.mem_cons, forall_eq_or_imp] at hsq
    rw [orthogonalizeNegOnes_cons, List.pairwise_cons]
    refine ⟨fun x hx ↦ ?_, pairwise_orthogonalizeNegOnes hB _ hsq.2⟩
    apply hB.eq_iff.mpr
    apply B.span_map_projectOffNegOne_le_ker c l hsq.1
    rw [← B.span_orthogonalizeNegOnes]
    exact subset_span hx
termination_by l.length

private theorem projectOffNegOnes_mem_orthogonal (hB : B.IsRefl) (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) (x : M) :
    B.projectOffNegOnes l x ∈ B.orthogonal (span R {y | y ∈ l}) := by
  cases l with
  | nil => simp [BilinForm.orthogonal]
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.mem_cons, forall_eq_or_imp] at hsq
    rw [← B.span_cons_map_projectOffNegOne, BilinForm.orthogonal,
      Submodule.mem_orthogonalBilin_span, projectOffNegOnes_cons, LinearMap.comp_apply]
    intro y hy
    rcases List.mem_cons.mp hy with heq | hy
    · subst y
      have hdiff : B (B.projectOffNegOne c x -
          B.projectOffNegOnes (l.map (B.projectOffNegOne c)) (B.projectOffNegOne c x)) c = 0 :=
        B.span_map_projectOffNegOne_le_ker c l hsq.1
          (B.sub_projectOffNegOnes_mem_span _ _)
      rw [LinearMap.map_sub₂, B.apply_projectOffNegOne_eq_zero hsq.1,
        zero_sub, neg_eq_zero] at hdiff
      exact hB.eq_iff.mpr hdiff
    · have h := projectOffNegOnes_mem_orthogonal hB
        (l.map (B.projectOffNegOne c)) hsq.2 (B.projectOffNegOne c x)
      exact Submodule.mem_orthogonalBilin_span.mp h hy
termination_by l.length

private theorem projectOffNegOnes_eq_self_of_mem_orthogonal (l : List M) (x : M)
    (hx : x ∈ B.flip.orthogonal (span R {y | y ∈ l})) :
    B.projectOffNegOnes l x = x := by
  cases l with
  | nil => simp
  | cons c l =>
    have hc : B x c = 0 := hx c (subset_span (List.mem_cons_self ..))
    rw [projectOffNegOnes_cons, LinearMap.comp_apply, projectOffNegOne_apply, hc, zero_smul,
      add_zero]
    refine projectOffNegOnes_eq_self_of_mem_orthogonal _ x ?_
    rw [← B.span_cons_map_projectOffNegOne] at hx
    exact B.flip.orthogonal_le (span_mono (fun _ hy ↦ List.mem_cons_of_mem _ hy)) hx
termination_by l.length

private theorem projectOffNegOnes_eq_zero_of_mem (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) {x : M} (hx : x ∈ l) :
    B.projectOffNegOnes l x = 0 := by
  cases l with
  | nil => exact (List.not_mem_nil hx).elim
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.mem_cons, forall_eq_or_imp] at hsq
    rw [projectOffNegOnes_cons, LinearMap.comp_apply]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hsq.1]
    · exact projectOffNegOnes_eq_zero_of_mem _ hsq.2 (List.mem_map_of_mem hx)
termination_by l.length

/-- The kernel of successive elimination is exactly the span of the original vectors. -/
theorem ker_projectOffNegOnes (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) :
    LinearMap.ker (B.projectOffNegOnes l) = span R {y | y ∈ l} := by
  refine le_antisymm (fun x hx ↦ ?_) (span_le.mpr (fun x hx ↦ ?_))
  · simpa only [LinearMap.mem_ker.mp hx, sub_zero] using B.sub_projectOffNegOnes_mem_span l x
  · exact B.projectOffNegOnes_eq_zero_of_mem l hsq hx

/-- Successive elimination is an idempotent with range the orthogonal complement of the
original vectors. -/
theorem isProj_projectOffNegOnes (hB : B.IsRefl) (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) :
    IsProj (B.orthogonal (span R {y | y ∈ l})) (B.projectOffNegOnes l) := by
  refine ⟨B.projectOffNegOnes_mem_orthogonal hB l hsq, fun x hx ↦ ?_⟩
  apply B.projectOffNegOnes_eq_self_of_mem_orthogonal
  intro y hy
  exact hB.eq_iff.mp (hx y hy)

/-- The span removed by successive elimination splits off as an orthogonal summand. -/
theorem isCompl_orthogonal_span_of_orthogonalizeNegOnes (hB : B.IsRefl) (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) :
    IsCompl (B.orthogonal (span R {y | y ∈ l})) (span R {y | y ∈ l}) :=
  B.ker_projectOffNegOnes l hsq ▸ (B.isProj_projectOffNegOnes hB l hsq).isCompl

/-- The successive updates agree with orthogonal projection away from the original span. -/
theorem projectOffNegOnes_eq_projection (hB : B.IsRefl) (l : List M)
    (hsq : ∀ c ∈ B.orthogonalizeNegOnes l, B c c = -1) :
    B.projectOffNegOnes l = (B.orthogonal (span R {y | y ∈ l})).projection
      (span R {y | y ∈ l}) (B.isCompl_orthogonal_span_of_orthogonalizeNegOnes hB l hsq) := by
  have hp := B.isProj_projectOffNegOnes hB l hsq
  simpa only [hp.range, B.ker_projectOffNegOnes l hsq] using
    IsIdempotentElem.eq_projection hp.isIdempotentElem

variable {C : BilinForm R N} (f : M →ₗ[R] N) (hf : ∀ x y, C (f x) (f y) = B x y)

include hf in
/-- A pairing-preserving linear map transports the updated classes, including when the map is
a quotient by relations in the radical. -/
theorem map_orthogonalizeNegOnes (l : List M) :
    (B.orthogonalizeNegOnes l).map f = C.orthogonalizeNegOnes (l.map f) := by
  cases l with
  | nil => simp
  | cons c l =>
    simp only [orthogonalizeNegOnes_cons, List.map_cons]
    congr 1
    rw [map_orthogonalizeNegOnes (l.map (B.projectOffNegOne c))]
    simp [List.map_map, Function.comp_def, hf]
termination_by l.length

include hf in
/-- Successive elimination commutes with any pairing-preserving linear map. -/
theorem map_projectOffNegOnes (l : List M) (x : M) :
    f (B.projectOffNegOnes l x) = C.projectOffNegOnes (l.map f) (f x) := by
  cases l with
  | nil => simp
  | cons c l =>
    simp only [projectOffNegOnes_cons, List.map_cons, LinearMap.comp_apply]
    rw [map_projectOffNegOnes (l.map (B.projectOffNegOne c))]
    simp [List.map_map, Function.comp_def, hf]
termination_by l.length

end LinearMap.BilinForm
