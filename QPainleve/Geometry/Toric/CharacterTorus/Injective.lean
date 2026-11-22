/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.NumberTheory.PadicVal.Units
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import TauCeti.Algebra.Group.FreeAbelianCharacter
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# Injective characters of free lattices

Send each basis vector to a distinct prime, viewed as a rational unit. The corresponding
prime valuations recover all the integer coordinates, so the character is injective.
Its values can be transported to any characteristic-zero field. With a distinguished
primitive vector, the character can take the value `1/2` there and distinct odd primes
on a complementary basis. The basis extension uses
`Module.Basis.exists_basis_finCons_of_apply_eq_one` from Tau Ceti, and
`TauCeti.freeAbelianCharEquiv` extends the assigned values to a character in basis coordinates.
-/

public noncomputable section

namespace QPainleve.CharacterTorus

open TauCeti

/-- For distinct assigned primes, the valuation at the prime assigned to an index recovers
the exponent at that index. -/
theorem ratUnitValuation_freeAbelianCharEquiv_symm {ι : Type*} (p : ι ↪ Nat.Primes)
    (i : ι) (x : ι →₀ ℤ) :
    ((p i).ratUnitValuation
      (freeAbelianCharEquiv.symm (fun j ↦ (p j).ratUnit) (Multiplicative.ofAdd x))).toAdd =
      x i := by
  classical
  have h : (p i).ratUnitValuation.comp (freeAbelianCharEquiv.symm (fun j ↦ (p j).ratUnit)) =
      (Finsupp.applyAddHom i : (ι →₀ ℤ) →+ ℤ).toMultiplicative := by
    apply freeAbelianCharEquiv.injective
    funext j
    rw [freeAbelianCharEquiv_comp, MulEquiv.apply_symm_apply, freeAbelianCharEquiv_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne hij,
        Nat.Primes.ratUnitValuation_ratUnit_of_ne (p.injective.ne hij)]
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h (Multiplicative.ofAdd x))

/-- The character determined by distinct rational prime units is injective. -/
theorem freeAbelianCharEquiv_symm_ratUnit_injective {ι : Type*} (p : ι ↪ Nat.Primes) :
    Function.Injective (freeAbelianCharEquiv.symm fun i ↦ (p i).ratUnit) := by
  intro x y h
  rw [← ofAdd_toAdd x, ← ofAdd_toAdd y] at h
  apply Multiplicative.toAdd.injective
  exact Finsupp.ext fun i ↦ by
    simpa only [ratUnitValuation_freeAbelianCharEquiv_symm] using
      congrArg (fun z ↦ ((p i).ratUnitValuation z).toAdd) h

variable {M k : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]
  [Field k] [CharZero k]

/-- A finite free integral lattice has an injective character with values in the units of
any characteristic-zero field. In particular, only the zero vector evaluates to one. -/
theorem exists_injective_character : ∃ a : Multiplicative M →* kˣ, Function.Injective a := by
  let b := Module.finBasis ℤ M
  let primes := @Nat.Subtype.orderIsoOfNat (Set.ofPred Nat.Prime)
    Nat.infinite_setOfPred_prime.to_subtype
  let p : Fin (Module.finrank ℤ M) ↪ Nat.Primes := Fin.valEmbedding.trans primes.toEquiv.toEmbedding
  let e := b.repr.toAddEquiv.toMultiplicative
  exact ⟨(Units.map (Rat.castHom k).toMonoidHom).comp
      ((freeAbelianCharEquiv.symm fun i ↦ (p i).ratUnit).comp e.toMonoidHom),
    (Units.map_injective Rat.cast_injective).comp
      ((freeAbelianCharEquiv_symm_ratUnit_injective p).comp e.injective)⟩

/-- A primitive vector can be the first element of a basis on which an injective character
takes the value `1/2` at the first vector and distinct odd prime values on all the others. -/
theorem exists_injective_character_of_primitive {δ : M} (f : M →ₗ[ℤ] ℤ) (hδ : f δ = 1) :
    ∃ (a : Multiplicative M →* kˣ) (n : ℕ) (b : Module.Basis (Fin (n + 1)) ℤ M)
      (p : Fin n ↪ Nat.Primes),
      Function.Injective a ∧ b 0 = δ ∧ (a (Multiplicative.ofAdd δ) : k) = (2 : k)⁻¹ ∧
        ∀ i, Odd (p i : ℕ) ∧ (a (Multiplicative.ofAdd (b i.succ)) : k) = (p i : ℕ) := by
  classical
  obtain rfl : ‹Module ℤ M› = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  obtain ⟨n, e⟩ := (LinearMap.ker f).basisOfPid (Module.finBasis ℤ M)
  obtain ⟨b, h0, -⟩ := Module.Basis.exists_basis_finCons_of_apply_eq_one hδ e
  let d := b.unitsSMul (Fin.cons (-1 : ℤˣ) (fun _ ↦ 1))
  have hd0 : d 0 = -δ := by
    rw [Module.Basis.unitsSMul_apply, Fin.cons_zero, Units.smul_def, h0]
    exact neg_one_smul ℤ δ
  have hds (i : Fin n) : d i.succ = b i.succ := by
    rw [Module.Basis.unitsSMul_apply, Fin.cons_succ, Units.smul_def]
    exact one_smul ℤ _
  let primes := @Nat.Subtype.orderIsoOfNat (Set.ofPred Nat.Prime)
    Nat.infinite_setOfPred_prime.to_subtype
  let p : Fin (n + 1) ↪ Nat.Primes := Fin.valEmbedding.trans primes.toEquiv.toEmbedding
  have hp0 : (p 0 : ℕ) = 2 :=
    (Nat.nth_apply_eq_orderIsoOfNat Nat.infinite_setOfPred_prime 0).symm.trans
      Nat.nth_prime_zero_eq_two
  let repr := d.repr.toAddEquiv.toMultiplicative
  let a : Multiplicative M →* kˣ :=
    (Units.map (Rat.castHom k).toMonoidHom).comp
      ((freeAbelianCharEquiv.symm fun i ↦ (p i).ratUnit).comp repr.toMonoidHom)
  have ha (i : Fin (n + 1)) :
      (a (Multiplicative.ofAdd (d i)) : k) = (p i : ℕ) := by
    have hrepr : repr (Multiplicative.ofAdd (d i)) =
        Multiplicative.ofAdd (Finsupp.single i 1) := congrArg Multiplicative.ofAdd (d.repr_self i)
    simp [a, hrepr]
  have ha0 : (a (Multiplicative.ofAdd (-δ)) : k) = 2 := by
    simpa only [hd0, hp0, Nat.cast_ofNat] using ha 0
  refine ⟨a, _, b, (Fin.succEmb n).trans p,
    (Units.map_injective Rat.cast_injective).comp
      ((freeAbelianCharEquiv_symm_ratUnit_injective p).comp repr.injective),
    h0, ?_, ?_⟩
  · rw [ofAdd_neg, map_inv, Units.val_inv_eq_inv_val] at ha0
    simpa only [inv_inv] using congrArg Inv.inv ha0
  · intro i
    refine ⟨(p i.succ).prop.odd_of_ne_two ?_, hds i ▸ ha i.succ⟩
    intro hi
    exact Fin.succ_ne_zero i (p.injective (Subtype.ext (hi.trans hp0.symm)))

end QPainleve.CharacterTorus
