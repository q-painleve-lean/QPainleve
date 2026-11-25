/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Injective
public import Mathlib.Basic.Complex.Basic

import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Avoiding countably many character values

An injective real-valued lattice character determines a real one-parameter family of
complex characters. On each nonidentity lattice element, the parameter determines the
value injectively. Countably many prescribed values therefore exclude only countably
many parameters.
-/

public section

open Multiplicative

namespace QPainleve.CharacterTorus

variable {M : Type*} [AddCommGroup M]

private noncomputable def expLogCharacter (a : Multiplicative M →* ℝˣ) (t : ℝ) :
    Multiplicative M →* ℂˣ where
  toFun x := Units.mk0 (Real.exp (t * Real.log (a x : ℝ)) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by
    simp only [Units.val_mk0, map_mul, Units.val_mul, Real.log_mul (a x).ne_zero (a y).ne_zero,
      mul_add, Real.exp_add, Complex.ofReal_mul])

private theorem log_ne_zero_of_character_injective [Module ℤ M] [Module.IsTorsionFree ℤ M]
    {a : Multiplicative M →* ℝˣ} (ha : Function.Injective a) {x : Multiplicative M} (hx : x ≠ 1) :
    Real.log (a x : ℝ) ≠ 0 := by
  intro h
  apply hx
  have hsq : (a x : ℝ) ^ 2 = 1 := by
    rcases Real.log_eq_zero.mp h with h₀ | h₁ | h₂
    · exact ((a x).ne_zero h₀).elim
    · simp [h₁]
    · norm_num [h₂]
  have hpow : x ^ 2 = 1 := ha (Units.ext (by simpa only [map_pow, Units.val_pow_eq_pow_val,
    map_one, Units.val_one] using hsq))
  have hzero : x.toAdd = 0 := (smul_eq_zero_iff_right (by decide : (2 : ℤ) ≠ 0)).mp (by
    simpa only [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_ofNat]
      using congrArg toAdd hpow)
  exact congrArg ofAdd hzero

variable [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- On countably many specified nonidentity lattice elements, a complex character
can simultaneously avoid a prescribed value at each occurrence. -/
theorem exists_character_avoiding {J : Type*} [Countable J] (x : J → Multiplicative M)
    (hx : ∀ j, x j ≠ 1) (v : J → ℂˣ) :
    ∃ a : Multiplicative M →* ℂˣ, ∀ j, a (x j) ≠ v j := by
  obtain ⟨a, ha⟩ := exists_injective_character (M := M) (k := ℝ)
  have hinj (j : J) : Function.Injective fun t ↦ expLogCharacter a t (x j) := by
    intro t u h
    have heq := Complex.ofReal_injective (congrArg Units.val h)
    exact mul_right_cancel₀ (log_ne_zero_of_character_injective ha (hx j))
      (Real.exp_injective heq)
  let bad (j : J) := {t : ℝ | expLogCharacter a t (x j) = v j}
  have hcount : (⋃ j, bad j).Countable := Set.countable_iUnion fun j ↦
    (Set.Subsingleton.countable fun _ h₁ _ h₂ ↦ hinj j (h₁.trans h₂.symm))
  have hproper : (⋃ j, bad j) ≠ Set.univ := fun h ↦ Set.not_countable_univ (h ▸ hcount)
  obtain ⟨t, ht⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  exact ⟨expLogCharacter a t, fun j h ↦ ht (Set.mem_iUnion.mpr ⟨j, h⟩)⟩

end QPainleve.CharacterTorus
