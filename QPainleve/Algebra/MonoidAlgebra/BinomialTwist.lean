/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Binomial twists of monoid algebras

Localizing at a binomial makes it possible to multiply each monomial by an integer
power of that binomial, even when the monomials themselves are not units. If the
exponent functional vanishes on the binomial's exponent, the inverse twist uses
the negative functional.
-/

public noncomputable section

open Multiplicative

namespace AddMonoidAlgebra

variable {R B : Type*} [CommSemiring R] [AddCommMonoid B]

local notation "A" => AddMonoidAlgebra R B
local notation "q(" a "," c "," b ")" => (single (0 : B) a + single b c)

/-- The distinguished unit in the localization at a constant plus a monomial. -/
def awayBinomialUnit (a c : R) (b : B) : (Localization.Away q(a,c,b))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away q(a,c,b)) q(a,c,b)).unit

/-- The value of the distinguished unit is the image of the binomial. -/
@[simp]
theorem coe_awayBinomialUnit (a c : R) (b : B) :
    (awayBinomialUnit a c b : Localization.Away q(a,c,b)) =
      algebraMap A (Localization.Away q(a,c,b)) q(a,c,b) :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit q(a,c,b))

variable (a c : R) (b : B)

local notation "S" => Localization.Away q(a,c,b)

private def binomialTwistOnAlgebra (f : B →+ ℤ) : A →ₐ[R] S :=
  lift R S B <|
    (algebraMap A S).toMonoidHom.comp (of R B) *
      ((Units.coeHom S).comp (zpowersHom Sˣ (awayBinomialUnit a c b))).comp f.toMultiplicative

private theorem binomialTwistOnAlgebra_single (f : B →+ ℤ) (x : B) (r : R) :
    binomialTwistOnAlgebra a c b f (single x r) =
      algebraMap A S (single x r) * ↑(awayBinomialUnit a c b ^ f x) := by
  rw [binomialTwistOnAlgebra, lift_single]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, of_apply, Units.coeHom_apply,
    zpowersHom_apply, toAdd_ofAdd]
  have h : r • (single x (1 : R) : A) = single x r := by simp [smul_single]
  -- Use the structural map as an algebra hom to move the coefficient inside.
  change r • (Algebra.algHom R A S (single x 1) * ↑(awayBinomialUnit a c b ^ f x)) =
    Algebra.algHom R A S (single x r) * ↑(awayBinomialUnit a c b ^ f x)
  rw [← smul_mul_assoc, ← map_smul, h]

private theorem binomialTwistOnAlgebra_binomial (f : B →+ ℤ) (hf : f b = 0) :
    binomialTwistOnAlgebra a c b f q(a,c,b) = algebraMap A S q(a,c,b) := by
  simp only [map_add, binomialTwistOnAlgebra_single, map_zero, hf, zpow_zero, Units.val_one,
    mul_one]

private def binomialTwistHom (f : B →+ ℤ) (hf : f b = 0) : S →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom q(a,c,b) (f := binomialTwistOnAlgebra a c b f) (by
    rw [binomialTwistOnAlgebra_binomial a c b f hf]
    exact IsLocalization.Away.algebraMap_isUnit _)

private theorem binomialTwistHom_algebraMap (f : B →+ ℤ) (hf : f b = 0) (x : A) :
    binomialTwistHom a c b f hf (algebraMap A S x) = binomialTwistOnAlgebra a c b f x := by
  rw [binomialTwistHom, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

private theorem binomialTwistHom_single (f : B →+ ℤ) (hf : f b = 0) (x : B) (r : R) :
    binomialTwistHom a c b f hf (algebraMap A S (single x r)) =
      algebraMap A S (single x r) * ↑(awayBinomialUnit a c b ^ f x) :=
  (binomialTwistHom_algebraMap a c b f hf _).trans (binomialTwistOnAlgebra_single a c b f x r)

private theorem binomialTwistHom_unit (f : B →+ ℤ) (hf : f b = 0) :
    Units.map (binomialTwistHom a c b f hf).toMonoidHom (awayBinomialUnit a c b) =
      awayBinomialUnit a c b := by
  apply Units.ext
  have h := (binomialTwistHom_algebraMap a c b f hf _).trans
    (binomialTwistOnAlgebra_binomial a c b f hf)
  simp only [Units.coe_map, coe_awayBinomialUnit]
  exact h

private theorem binomialTwistHom_comp_neg (f : B →+ ℤ) (hf : f b = 0) :
    (binomialTwistHom a c b f hf).comp (binomialTwistHom a c b (-f) (by simp [hf])) =
      AlgHom.id R S := by
  apply Localization.algHom_ext
  apply (lift R S B).symm.injective
  apply MonoidHom.ext
  intro x
  -- The localization extensionality lemma precomposes with the structural algebra map.
  change binomialTwistHom a c b f hf
      (binomialTwistHom a c b (-f) (by simp [hf]) (algebraMap A S (single x.toAdd 1))) =
    algebraMap A S (single x.toAdd 1)
  rw [binomialTwistHom_single, map_mul]
  have h (n : ℤ) : binomialTwistHom a c b f hf (↑(awayBinomialUnit a c b ^ n)) =
      (↑(awayBinomialUnit a c b ^ n) : S) := by
    have he := congrArg (fun u : Sˣ ↦ (u : S)) (show
        Units.map (binomialTwistHom a c b f hf).toMonoidHom (awayBinomialUnit a c b ^ n) =
          awayBinomialUnit a c b ^ n by rw [map_zpow, binomialTwistHom_unit])
    exact he
  rw [h, binomialTwistHom_single, mul_assoc, ← Units.val_mul, ← zpow_add]
  simp only [AddMonoidHom.neg_apply, add_neg_cancel, zpow_zero, Units.val_one, mul_one]

/-- Multiply each monomial by the power of the localized binomial specified by the
exponent functional. The requirement that the functional vanish on the binomial's
exponent fixes the binomial. -/
def binomialTwist (f : B →+ ℤ) (hf : f b = 0) : S ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (binomialTwistHom a c b f hf) (binomialTwistHom a c b (-f) (by simp [hf]))
    (binomialTwistHom_comp_neg a c b f hf)
    (by simpa only [neg_neg] using binomialTwistHom_comp_neg a c b (-f) (by simp [hf]))

/-- The action on a monomial with arbitrary coefficient. -/
@[simp]
theorem binomialTwist_single (f : B →+ ℤ) (hf : f b = 0) (x : B) (r : R) :
    binomialTwist a c b f hf (algebraMap A S (single x r)) =
      algebraMap A S (single x r) * ↑(awayBinomialUnit a c b ^ f x) :=
  binomialTwistHom_single a c b f hf x r

/-- The twist fixes the distinguished unit. -/
@[simp]
theorem binomialTwist_unit (f : B →+ ℤ) (hf : f b = 0) :
    Units.map (↑(binomialTwist a c b f hf).toMulEquiv : S →* S) (awayBinomialUnit a c b) =
      awayBinomialUnit a c b :=
  binomialTwistHom_unit a c b f hf

/-- Negating the functional gives the inverse twist. -/
@[simp]
theorem binomialTwist_symm (f : B →+ ℤ) (hf : f b = 0) :
    (binomialTwist a c b f hf).symm = binomialTwist a c b (-f) (by simp [hf]) :=
  AlgEquiv.ext fun _ ↦ rfl

end AddMonoidAlgebra
