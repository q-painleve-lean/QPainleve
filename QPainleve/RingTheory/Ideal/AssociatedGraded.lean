/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import TauCeti.RingTheory.GradedAlgebra.DirectSum
public import TauCeti.RingTheory.Ideal.AssociatedGraded

/-!
# The internal grading of an associated graded ring

The degree-`n` summand of `Ideal.AssociatedGraded I` is a submodule over the quotient ring
`R ⧸ I`. The internal grading reuses the direct-sum grading on `DirectSum.summand`, allowing
constructions such as `Proj` to use the existing direct-sum ring.
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
