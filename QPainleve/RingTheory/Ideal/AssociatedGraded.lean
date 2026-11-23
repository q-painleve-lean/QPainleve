/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import TauCeti.RingTheory.GradedAlgebra.DirectSum
public import TauCeti.RingTheory.Ideal.AssociatedGraded

/-!
# Associated graded rings of ideals

The degree-`n` summand of `Ideal.AssociatedGraded I` is a submodule over the quotient ring
`R ⧸ I`. The internal grading reuses the direct-sum grading on `DirectSum.summand`, allowing
constructions such as `Proj` to use the existing direct-sum ring.

When the associated graded ring has no zero divisors, powers of an order-one element
shift ideal-power membership by their degree.
-/

public section

namespace Ideal.AssociatedGraded

open DirectSum

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The image of the degree-`n` summand in the associated graded ring. -/
noncomputable def grade (n : ℕ) : Submodule (R ⧸ I) I.AssociatedGraded where
  __ := (summand R I.GradedPiece n).toAddSubmonoid
  smul_mem' := by
    intro c x hx
    obtain ⟨a, rfl⟩ := mem_summand.mp hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact mem_summand.mpr ⟨r • a, (of_smul R n r a).trans
      (IsScalarTower.algebraMap_smul (R ⧸ I) r _).symm⟩

/-- Membership in the internal grading means lying in the corresponding external summand. -/
theorem mem_grade_iff {n : ℕ} {x : I.AssociatedGraded} :
    x ∈ grade I n ↔ x ∈ Set.range (DirectSum.of I.GradedPiece n) :=
  mem_summand

/-- The degree-`n` summand maps into the degree-`n` submodule. -/
@[simp]
theorem of_mem_grade (n : ℕ) (x : I.GradedPiece n) :
    DirectSum.of I.GradedPiece n x ∈ grade I n :=
  (mem_grade_iff I).2 ⟨x, rfl⟩

/-- Changing the scalar ring to the quotient leaves the additive summands unchanged. -/
@[simp]
theorem grade_toAddSubmonoid (n : ℕ) :
    (grade I n).toAddSubmonoid = (summand R I.GradedPiece n).toAddSubmonoid :=
  (rfl)

/-- The canonical internal grading of the associated graded ring. -/
noncomputable instance : GradedAlgebra (grade I) := by
  have d : GradedRing (fun n ↦ (grade I n).toAddSubmonoid) := by
    simp only [grade_toAddSubmonoid]
    let d₀ : GradedAlgebra (summand R I.GradedPiece) := inferInstance
    exact { d₀ with }
  exact { d with }

end Ideal.AssociatedGraded

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R} {a : R}

/-- If the initial form of `a` has degree one and the associated graded ring has no zero
divisors, multiplying by `a ^ n` raises every ideal-power membership threshold by `n`. -/
theorem pow_mul_mem_pow_add_iff_of_notMem_sq [NoZeroDivisors I.AssociatedGraded]
    (ha : a ∈ I) (ha₂ : a ∉ I ^ 2) (n m : ℕ) (x : R) :
    a ^ n * x ∈ I ^ (n + m) ↔ x ∈ I ^ m := by
  have step (y : R) (j : ℕ) : a * y ∈ I ^ (j + 1) → y ∈ I ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      intro h
      have hx := ih (Ideal.pow_le_pow_right (Nat.le_succ _) h)
      by_contra hx'
      exact AssociatedGraded.mul_notMem_pow_succ (by simpa using ha) ha₂ hx hx'
        (by simpa [Nat.add_comm 1 j] using h)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, Nat.succ_add]
    exact ⟨fun h ↦ ih.mp (step _ _ h), fun h ↦ by
      rw [pow_succ']
      exact mul_mem_mul ha (ih.mpr h)⟩

end Ideal
