/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

import Mathlib.Algebra.BigOperators.Fin
import QPainleve.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Avoiding countably many character values

Choose the values of a lattice character on a basis by induction. Once the other
coordinates are chosen, each constraint with nonzero exponent in the first coordinate
excludes only finitely many choices for that coordinate.
-/

public section

open Multiplicative

namespace QPainleve.CharacterTorus

variable {k : Type*} [Field k]

variable [Uncountable k]

private theorem exists_coordinates_avoiding {n : ℕ} {J : Type*} [Countable J]
    (e : J → Fin n → ℤ) (he : ∀ j, e j ≠ 0) (v : J → kˣ) :
    ∃ a : Fin n → kˣ, ∀ j, (∏ i, a i ^ e j i) ≠ v j := by
  induction n generalizing J with
  | zero => exact ⟨fun _ ↦ 1, fun j ↦ (he j (Subsingleton.elim _ _)).elim⟩
  | succ n ih =>
    let J₀ := {j : J // e j 0 = 0}
    obtain ⟨a, ha⟩ := ih (J := J₀) (fun j i ↦ e j i.succ) (fun j h ↦ he j (by
      funext i
      exact Fin.cases j.property (fun i ↦ congrFun h i) i)) (fun j ↦ v j)
    let J₁ := {j : J // e j 0 ≠ 0}
    let bad : Set kˣ := ⋃ j : J₁, {u | u ^ e j 0 = v j / ∏ i, a i ^ e j i.succ}
    have hbad : bad.Countable := Set.countable_iUnion fun j : J₁ ↦
      (Units.finite_setOf_zpow_eq j.property _).countable
    have hcount : (insert (0 : k) (Units.val '' bad)).Countable := (hbad.image _).insert _
    have hproper : insert (0 : k) (Units.val '' bad) ≠ Set.univ :=
      fun h ↦ Set.not_countable_univ (h ▸ hcount)
    obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
    let u := Units.mk0 t (fun h ↦ ht (Set.mem_insert_iff.mpr (Or.inl h)))
    refine ⟨Fin.cons u a, fun j hj ↦ ?_⟩
    rw [Fin.prod_univ_succ] at hj
    simp only [Fin.cons_zero, Fin.cons_succ] at hj
    by_cases h : e j 0 = 0
    · exact ha ⟨j, h⟩ (by simpa [h] using hj)
    · have hu : u ∈ bad := Set.mem_iUnion.mpr ⟨⟨j, h⟩, eq_div_iff_mul_eq'.mpr hj⟩
      exact ht (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)

/-- Over an uncountable field, a lattice character can simultaneously avoid a prescribed
value at each of countably many nonidentity lattice elements. -/
theorem exists_character_avoiding {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] {J : Type*} [Countable J] (x : J → Multiplicative M)
    (hx : ∀ j, x j ≠ 1) (v : J → kˣ) : ∃ a : Multiplicative M →* kˣ, ∀ j, a (x j) ≠ v j := by
  let b := Module.finBasis ℤ M
  obtain ⟨a, ha⟩ := exists_coordinates_avoiding (fun j i ↦ b.repr ((x j).toAdd) i)
    (fun j h ↦ hx j (toAdd.injective (show (x j).toAdd = 0 from
      b.repr.injective ((Finsupp.ext fun i ↦ congrFun h i).trans b.repr.map_zero.symm)))) v
  refine ⟨TauCeti.freeAbelianCharEquiv.symm a |>.comp
    b.repr.toAddEquiv.toMultiplicative.toMonoidHom, fun j ↦ ?_⟩
  change TauCeti.freeAbelianCharEquiv.symm a (ofAdd (b.repr (x j).toAdd)) ≠ v j
  rw [TauCeti.freeAbelianCharEquiv_symm_apply_ofAdd, Finsupp.prod_fintype]
  · exact ha j
  · intro i
    simp

end QPainleve.CharacterTorus
