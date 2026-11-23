/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic
import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# Fixed and moving parts of linear systems

The fixed part of a nonempty system of effective Weil divisors is the largest common effective
subdivisor. Subtracting it leaves a system in which every prime divisor is absent from some member.
For a complete linear system the residual system is again complete.

## References

* P. Hacking, *583C Lecture notes*, §7.2.
-/

public section

namespace TauCeti.AlgebraicGeometry.WeilDivisor

noncomputable section

variable {X : Type*} {S : Set (WeilDivisor X)}

private lemma bddBelow_coeff_image (hS : ∀ D ∈ S, 0 ≤ D) (x : X) :
    BddBelow ((fun D : WeilDivisor X ↦ D x) '' S) :=
  ⟨0, by rintro _ ⟨D, hD, rfl⟩; exact coeff_nonneg (hS D hD) x⟩

/-- The fixed part of a nonempty family of effective Weil divisors, with each coefficient
equal to the least coefficient at that prime in the family. -/
def fixedPart (S : Set (WeilDivisor X)) (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x ↦ sInf ((fun D : WeilDivisor X ↦ D x) '' S)) (by
    obtain ⟨D, hD⟩ := hne
    refine D.support.finite_toSet.subset fun x hx ↦ Finsupp.mem_support_iff.mpr fun hDx ↦ hx ?_
    exact le_antisymm ((csInf_le (bddBelow_coeff_image hS x) ⟨D, hD, rfl⟩).trans_eq hDx)
      (le_csInf ⟨D x, D, hD, rfl⟩ fun _ ⟨E, hE, h⟩ ↦
        h ▸ coeff_nonneg (hS E hE) x))

/-- The coefficient of the fixed part is the minimum of the coefficients of the family. -/
lemma isLeast_coeff_fixedPart (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) (x : X) :
    IsLeast ((fun D : WeilDivisor X ↦ D x) '' S) (fixedPart S hne hS x) := by
  rw [fixedPart, Finsupp.ofSupportFinite_coe]
  exact ⟨Int.csInf_mem (hne.image _) (bddBelow_coeff_image hS x),
    fun _ h ↦ csInf_le (bddBelow_coeff_image hS x) h⟩

/-- Each coefficient of the fixed part is attained by a member of the system. -/
lemma exists_coeff_eq_fixedPart (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) (x : X) :
    ∃ D ∈ S, D x = fixedPart S hne hS x :=
  (isLeast_coeff_fixedPart hne hS x).1

/-- The fixed part is effective. -/
lemma fixedPart_nonneg (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    0 ≤ fixedPart S hne hS := by
  refine Finsupp.le_def.mpr fun x ↦ ?_
  obtain ⟨D, hD, h⟩ := exists_coeff_eq_fixedPart hne hS x
  exact (coeff_nonneg (hS D hD) x).trans_eq h

/-- The fixed part is the greatest lower bound of the family in the coefficientwise order. -/
theorem isGLB_fixedPart (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    IsGLB S (fixedPart S hne hS) := by
  refine ⟨fun D hD x ↦ (isLeast_coeff_fixedPart hne hS x).2 ⟨D, hD, rfl⟩, fun E hE x ↦ ?_⟩
  obtain ⟨D, hD, h⟩ := exists_coeff_eq_fixedPart hne hS x
  exact h ▸ hE hD x

/-- A divisor is bounded by the fixed part exactly when it is bounded by every member. -/
lemma le_fixedPart_iff (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) {E : WeilDivisor X} :
    E ≤ fixedPart S hne hS ↔ ∀ D ∈ S, E ≤ D :=
  le_isGLB_iff (isGLB_fixedPart hne hS)

/-- The fixed part is zero exactly when each prime is absent from some member. -/
lemma fixedPart_eq_zero_iff (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    fixedPart S hne hS = 0 ↔ ∀ x, ∃ D ∈ S, D x = 0 := by
  constructor
  · intro h x
    simpa only [h, Finsupp.zero_apply] using exists_coeff_eq_fixedPart hne hS x
  · intro h
    refine le_antisymm (fun x ↦ ?_) (fixedPart_nonneg hne hS)
    obtain ⟨D, hD, hDx⟩ := h x
    exact ((isGLB_fixedPart hne hS).1 hD x).trans_eq hDx

/-- The moving part of a system consists of the divisors left by removing its fixed part. -/
def movingPart (S : Set (WeilDivisor X)) (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    Set (WeilDivisor X) :=
  (fun D ↦ D - fixedPart S hne hS) '' S

/-- A divisor belongs to the moving system when adding back the fixed part recovers a member
of the original system. -/
@[simp]
lemma mem_movingPart_iff (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) {E : WeilDivisor X} :
    E ∈ movingPart S hne hS ↔ E + fixedPart S hne hS ∈ S := by
  simp [movingPart, sub_eq_iff_eq_add]

/-- The moving system is nonempty. -/
lemma movingPart_nonempty (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) :
    (movingPart S hne hS).Nonempty :=
  hne.image _

/-- Removing the fixed part leaves effective divisors. -/
lemma nonneg_of_mem_movingPart (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) {E : WeilDivisor X}
    (hE : E ∈ movingPart S hne hS) : 0 ≤ E :=
  nonneg_of_le_add_left <| (isGLB_fixedPart hne hS).1 ((mem_movingPart_iff hne hS).mp hE)

/-- Each prime is absent from some member of the moving system. -/
theorem exists_mem_movingPart_apply_eq_zero (hne : S.Nonempty) (hS : ∀ D ∈ S, 0 ≤ D) (x : X) :
    ∃ E ∈ movingPart S hne hS, E x = 0 := by
  obtain ⟨D, hD, h⟩ := exists_coeff_eq_fixedPart hne hS x
  exact ⟨D - fixedPart S hne hS, ⟨D, hD, rfl⟩, by rw [Finsupp.sub_apply, h, sub_self]⟩

namespace OrderSystem

variable {G : Type*} [AddCommGroup G] (P : OrderSystem X G)

/-- Removing the fixed part of a complete linear system gives the complete linear system
of the difference. -/
theorem movingPart_completeLinearSystem (D : WeilDivisor X)
    (hne : (P.completeLinearSystem D).Nonempty) :
    let hS : ∀ E ∈ P.completeLinearSystem D, 0 ≤ E :=
      fun _ hE ↦ P.nonneg_of_mem_completeLinearSystem hE
    movingPart (P.completeLinearSystem D) hne hS =
      P.completeLinearSystem (D - fixedPart (P.completeLinearSystem D) hne hS) := by
  intro hS
  let F := fixedPart (P.completeLinearSystem D) hne hS
  ext E
  constructor
  · intro hE
    have hclass := P.divisorClass_eq_of_mem_completeLinearSystem ((mem_movingPart_iff hne hS).mp hE)
    exact P.mem_completeLinearSystem_iff_divisorClass.mpr
      ⟨nonneg_of_mem_movingPart hne hS hE, by rw [map_sub, ← hclass, map_add, add_sub_cancel_right]⟩
  · intro hE
    have ⟨hEeff, hEclass⟩ := P.mem_completeLinearSystem_iff_divisorClass.mp hE
    refine (mem_movingPart_iff hne hS).mpr <| P.mem_completeLinearSystem_iff_divisorClass.mpr
      ⟨add_nonneg hEeff (fixedPart_nonneg hne hS), ?_⟩
    rw [map_add, ← hEclass, map_sub, sub_add_cancel]

end OrderSystem

end

end TauCeti.AlgebraicGeometry.WeilDivisor
