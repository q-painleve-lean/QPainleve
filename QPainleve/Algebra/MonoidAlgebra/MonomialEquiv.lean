/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Monomial isomorphisms of group algebras

Over a domain, the units of a group algebra with unique two-term exponent sums determine the
shape of every algebra isomorphism. Each such isomorphism is a character twist followed by
a change of exponents. The classification uses Tau Ceti's `AddMonoidAlgebra.unitsEquiv`
and `MonoidAlgebra.charTwist`.
-/

public noncomputable section

namespace AddMonoidAlgebra

variable {R A B C : Type*} [CommSemiring R]

section Construction

variable [AddMonoid A] [AddMonoid B] [AddMonoid C]

/-- Multiply each monomial by its character value and then change its exponent. -/
def monomialAlgEquiv (χ : Multiplicative A →* Rˣ) (e : A ≃+ B) :
    AddMonoidAlgebra R A ≃ₐ[R] AddMonoidAlgebra R B :=
  (toMultiplicativeAlgEquiv R R A).trans <|
    (MonoidAlgebra.charTwist χ).trans <|
      (toMultiplicativeAlgEquiv R R A).symm.trans (domCongr R R e)

/-- The coefficient of a monomial is multiplied by the character at its original exponent. -/
@[simp]
theorem monomialAlgEquiv_single (χ : Multiplicative A →* Rˣ) (e : A ≃+ B) (a : A) (r : R) :
    monomialAlgEquiv χ e (single a r) = single (e a) ((χ (.ofAdd a) : R) * r) := by
  simp only [monomialAlgEquiv, AlgEquiv.trans_apply, toMultiplicativeAlgEquiv_single,
    MonoidAlgebra.charTwist_single]
  rw [← toMultiplicativeAlgEquiv_single (R := R) a, AlgEquiv.symm_apply_apply, domCongr_single]

/-- The trivial character leaves only the exponent change. -/
@[simp]
theorem monomialAlgEquiv_one (e : A ≃+ B) :
    monomialAlgEquiv (1 : Multiplicative A →* Rˣ) e = domCongr R R e := by
  ext x
  simp [monomialAlgEquiv]

/-- In a composite, the second character is pulled back along the first exponent change. -/
theorem monomialAlgEquiv_trans (χ : Multiplicative A →* Rˣ) (ψ : Multiplicative B →* Rˣ)
    (e : A ≃+ B) (f : B ≃+ C) :
    (monomialAlgEquiv χ e).trans (monomialAlgEquiv ψ f) =
      monomialAlgEquiv (χ * ψ.comp e.toAddMonoidHom.toMultiplicative) (e.trans f) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply algHom_ext
  · intro a
    simp [mul_comm]
  · exact Subsingleton.elim _ _

/-- The inverse uses the inverse character pulled back along the inverse exponent change. -/
@[simp]
theorem monomialAlgEquiv_symm (χ : Multiplicative A →* Rˣ) (e : A ≃+ B) :
    (monomialAlgEquiv χ e).symm =
      monomialAlgEquiv (χ⁻¹.comp e.symm.toAddMonoidHom.toMultiplicative) e.symm := by
  have h := monomialAlgEquiv_trans χ (χ⁻¹.comp e.symm.toAddMonoidHom.toMultiplicative) e e.symm
  have hχ : χ * (χ⁻¹.comp e.symm.toAddMonoidHom.toMultiplicative).comp
      e.toAddMonoidHom.toMultiplicative = 1 := by
    ext a
    simp
  rw [hχ, monomialAlgEquiv_one, AddEquiv.self_trans_symm, domCongr_refl] at h
  exact AlgEquiv.ext fun b ↦ by
    simpa using (DFunLike.congr_fun h ((monomialAlgEquiv χ e).symm b)).symm

end Construction

section Classification

variable [AddGroup A] [AddGroup B] [Nontrivial R] [NoZeroDivisors R] [TwoUniqueSums B]

private def monomialData (f : AddMonoidAlgebra R A →ₐ[R] AddMonoidAlgebra R B) :
    Multiplicative A →* Rˣ × Multiplicative (AddUnits B) :=
  unitsEquiv.toMonoidHom.comp (f.toMonoidHom.comp (of R A)).toHomUnits

private def monomialExponent (f : AddMonoidAlgebra R A →ₐ[R] AddMonoidAlgebra R B) : A →+ B :=
  (AddUnits.coeHom B).comp (MonoidHom.snd _ _ |>.comp (monomialData f)).toAdditive

private def monomialCharacter (f : AddMonoidAlgebra R A →ₐ[R] AddMonoidAlgebra R B) :
    Multiplicative A →* Rˣ :=
  (MonoidHom.fst _ _).comp (monomialData f)

private theorem map_single_monomialData (f : AddMonoidAlgebra R A →ₐ[R] AddMonoidAlgebra R B)
    (a : A) (r : R) :
    f (single a r) = single (monomialExponent f a) ((monomialCharacter f (.ofAdd a) : R) * r) := by
  have h := val_eq_single_unitsEquiv ((f.toMonoidHom.comp (of R A)).toHomUnits (.ofAdd a))
  have h₁ :
      f (single a 1) = single (monomialExponent f a) (monomialCharacter f (.ofAdd a) : R) := by
    unfold monomialExponent monomialCharacter monomialData
    exact h
  calc
    f (single a r) = f (r • single a 1) := by rw [smul_single, smul_eq_mul, mul_one]
    _ = single (monomialExponent f a) ((monomialCharacter f (.ofAdd a) : R) * r) := by
      rw [map_smul, h₁, smul_single, smul_eq_mul, mul_comm]

variable [TwoUniqueSums A]

private theorem monomialExponent_leftInverse
    (f : AddMonoidAlgebra R A ≃ₐ[R] AddMonoidAlgebra R B) :
    Function.LeftInverse (monomialExponent f.symm.toAlgHom) (monomialExponent f.toAlgHom) := by
  intro a
  have h := f.symm_apply_apply (single a (1 : R))
  simp only [← AlgEquiv.toAlgHom_apply, map_single_monomialData] at h
  exact ((single_inj.mp h).resolve_right fun hzero ↦ one_ne_zero hzero.2).1

/-- Every algebra isomorphism of these group algebras has a unique character and exponent
equivalence giving its monomial action. -/
theorem existsUnique_monomialAlgEquiv (f : AddMonoidAlgebra R A ≃ₐ[R] AddMonoidAlgebra R B) :
    ∃! p : (Multiplicative A →* Rˣ) × (A ≃+ B), monomialAlgEquiv p.1 p.2 = f := by
  let e : A ≃+ B :=
    { monomialExponent f.toAlgHom with
      invFun := monomialExponent f.symm.toAlgHom
      left_inv := monomialExponent_leftInverse f
      right_inv := monomialExponent_leftInverse f.symm }
  let χ := monomialCharacter f.toAlgHom
  have h : monomialAlgEquiv χ e = f := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply algHom_ext
    · intro a
      rw [AlgEquiv.toAlgHom_apply, monomialAlgEquiv_single, map_single_monomialData]
      rfl
    · exact Subsingleton.elim _ _
  refine ⟨(χ, e), h, fun p hp ↦ ?_⟩
  have hsingle (a : A) := congrArg (fun g : AddMonoidAlgebra R A ≃ₐ[R] AddMonoidAlgebra R B ↦
    g (single a 1)) (hp.trans h.symm)
  simp only [monomialAlgEquiv_single, mul_one] at hsingle
  have hp' (a : A) :=
    (single_inj.mp (hsingle a)).resolve_right fun hz ↦ (p.1 (.ofAdd a)).ne_zero hz.1
  exact Prod.ext
    (MonoidHom.ext fun a ↦ Units.ext (hp' a.toAdd).2)
    (AddEquiv.ext fun a ↦ (hp' a).1)

end Classification

end AddMonoidAlgebra
