/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.NumberTheory.Prime.Units
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# Injective characters of free lattices

Send each basis vector to a distinct prime, viewed as a rational unit. Mathlib's
`Rat.padicValuation` recovers the integer coordinates, so the character is injective.
Its values can be transported to any characteristic-zero field. With a distinguished
primitive vector, the character can take the value `1/2` there and distinct odd primes
on a complementary basis. The basis extension uses
`Module.Basis.exists_basis_finCons_of_apply_eq_one` from Tau Ceti.
-/

public noncomputable section

namespace Module.Basis

variable {ι M : Type*} [AddCommGroup M] [Module ℤ M]

/-- Map the elements of an integral basis to the prescribed rational prime units. -/
def primeCharacter (b : Basis ι ℤ M) (p : ι → Nat.Primes) :
    Multiplicative M →* ℚˣ :=
  (b.constr ℤ (fun i ↦ Additive.ofMul (p i).ratUnit)).toAddMonoidHom.toMultiplicativeLeft

@[simp]
theorem primeCharacter_apply_basis (b : Basis ι ℤ M) (p : ι → Nat.Primes) (i : ι) :
    b.primeCharacter p (Multiplicative.ofAdd (b i)) = (p i).ratUnit := by
  exact congrArg Additive.toMul (b.constr_basis ℤ (fun j ↦ Additive.ofMul (p j).ratUnit) i)

/-- The multiplicative valuation at the assigned prime is the exponential of the negative
basis coordinate when the primes are distinct. -/
theorem padicValuation_primeCharacter (b : Basis ι ℤ M) (p : ι ↪ Nat.Primes)
    (i : ι) (x : M) :
    @Rat.padicValuation (p i) ⟨(p i).prop⟩ (b.primeCharacter p (Multiplicative.ofAdd x) : ℚ) =
      WithZero.exp (-b.repr x i) := by
  classical
  obtain rfl : ‹Module ℤ M› = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  let : Fact (p i : ℕ).Prime := ⟨(p i).prop⟩
  let v := Rat.padicValuation (p i)
  have hprod : b.primeCharacter p (Multiplicative.ofAdd x) =
      (b.repr x).prod fun j n ↦ (p j).ratUnit ^ n := by
    conv_lhs => rw [← b.linearCombination_repr x]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.prod, ofAdd_sum, map_prod,
      ofAdd_zsmul, map_zpow, primeCharacter_apply_basis]
  calc
    _ = (v.toMonoidHom.comp (Units.coeHom ℚ)) (b.primeCharacter p (Multiplicative.ofAdd x)) :=
      rfl
    _ = (b.repr x).prod (fun j n ↦ v (↑((p j).ratUnit ^ n : ℚˣ))) := by
      rw [hprod, map_finsuppProd]
      rfl
    _ = _ := by
      rw [Finsupp.prod_eq_single i]
      · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Nat.Primes.coe_ratUnit]
        dsimp only [v]
        rw [Rat.padicValuation_self, ← WithZero.exp_zsmul]
        simp
      · intro j _ hji
        have hval : v ((p j).ratUnit : ℚ) = 1 := by
          dsimp only [v]
          rw [Nat.Primes.coe_ratUnit, Rat.padicValuation_natCast, Int.padicValuation_eq_one_iff,
            Int.natCast_dvd_natCast, (p j).prop.dvd_iff_eq (p i).prop.ne_one]
          exact Nat.Primes.coe_nat_injective.ne (p.injective.ne hji)
        rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hval, one_zpow]
      · simp

/-- The prime character of a basis with distinct assigned primes is injective. -/
theorem primeCharacter_injective (b : Basis ι ℤ M) (p : ι ↪ Nat.Primes) :
    Function.Injective (b.primeCharacter p) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply b.repr.injective
  ext i
  let : Fact (p i : ℕ).Prime := ⟨(p i).prop⟩
  have hval := congrArg (fun z : ℚˣ ↦ Rat.padicValuation (p i) (z : ℚ)) h
  exact neg_injective (WithZero.exp_injective
    ((padicValuation_primeCharacter b p i x.toAdd).symm.trans
      (hval.trans (padicValuation_primeCharacter b p i y.toAdd))))

end Module.Basis

namespace QPainleve.CharacterTorus

variable {M k : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]
  [Field k] [CharZero k]

/-- A finite free integral lattice has an injective character with values in the units of
any characteristic-zero field. In particular, only the zero vector evaluates to one. -/
theorem exists_injective_character : ∃ a : Multiplicative M →* kˣ, Function.Injective a := by
  let b := Module.finBasis ℤ M
  let e := @Nat.Subtype.orderIsoOfNat (Set.ofPred Nat.Prime)
    Nat.infinite_setOfPred_prime.to_subtype
  let p : Fin (Module.finrank ℤ M) ↪ Nat.Primes := Fin.valEmbedding.trans e.toEquiv.toEmbedding
  exact ⟨(Units.map (Rat.castHom k).toMonoidHom).comp (b.primeCharacter p),
    (Units.map_injective Rat.cast_injective).comp (b.primeCharacter_injective p)⟩

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
  let a : Multiplicative M →* kˣ :=
    (Units.map (Rat.castHom k).toMonoidHom).comp (d.primeCharacter p)
  have ha (i : Fin (n + 1)) :
      (a (Multiplicative.ofAdd (d i)) : k) = (p i : ℕ) := by
    simp [a]
  have ha0 : (a (Multiplicative.ofAdd (-δ)) : k) = 2 := by
    simpa only [hd0, hp0, Nat.cast_ofNat] using ha 0
  refine ⟨a, _, b, (Fin.succEmb n).trans p,
    (Units.map_injective Rat.cast_injective).comp (d.primeCharacter_injective p), h0, ?_, ?_⟩
  · rw [ofAdd_neg, map_inv, Units.val_inv_eq_inv_val] at ha0
    simpa only [inv_inv] using congrArg Inv.inv ha0
  · intro i
    refine ⟨(p i.succ).prop.odd_of_ne_two ?_, hds i ▸ ha i.succ⟩
    intro hi
    exact Fin.succ_ne_zero i (p.injective (Subtype.ext (hi.trans hp0.symm)))

end QPainleve.CharacterTorus
