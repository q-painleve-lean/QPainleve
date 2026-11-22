/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CharacterTwist
public import TauCeti.Algebra.MonoidAlgebra.Units

/-!
# Isomorphisms of group algebras with monomial units

When every unit is a monomial, an algebra isomorphism takes each basis monomial to a basis
monomial scaled by a unit. The exponents define an isomorphism of the exponent groups, and
the scaling factors define a character of the source exponent group. The construction uses
`MonoidAlgebra.unitsEquiv` to recover these two pieces of data and `MonoidAlgebra.charTwist`
to realize the scaling. In particular this gives the coordinate-ring description of
isomorphisms of split tori.
-/

public noncomputable section

namespace MonoidAlgebra

variable {k G H : Type*} [CommSemiring k] [Nontrivial k] [NoZeroDivisors k]
variable [Group G] [Group H] [TwoUniqueProds G] [TwoUniqueProds H]

private def monomialData (f : MonoidAlgebra k G →ₐ[k] MonoidAlgebra k H) : G →* kˣ × Hˣ :=
  unitsEquiv.toMonoidHom.comp (f.toMonoidHom.comp (of k G)).toHomUnits

private def exponentHom (f : MonoidAlgebra k G →ₐ[k] MonoidAlgebra k H) : G →* H :=
  (Units.coeHom H).comp ((MonoidHom.snd _ _).comp (monomialData f))

omit [TwoUniqueProds G] in
private theorem apply_single_eq (f : MonoidAlgebra k G →ₐ[k] MonoidAlgebra k H)
    (a : G) (r : k) :
    f (single a r) = single (exponentHom f a) ((monomialData f a).1.val * r) := by
  have h : f (single a 1) = single (exponentHom f a) (monomialData f a).1.val :=
    val_eq_single_unitsEquiv ((f.toMonoidHom.comp (of k G)).toHomUnits a)
  calc
    f (single a r) = r • f (single a 1) := by rw [← map_smul, smul_single, smul_eq_mul, mul_one]
    _ = _ := by rw [h, smul_single, smul_eq_mul, mul_comm]

private theorem exponentHom_leftInverse (e : MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k H) :
    Function.LeftInverse (exponentHom e.symm.toAlgHom) (exponentHom e.toAlgHom) := by
  intro a
  have h := e.symm_apply_apply (single a (1 : k))
  rw [← AlgEquiv.coe_toAlgHom e, apply_single_eq, ← AlgEquiv.coe_toAlgHom e.symm,
    apply_single_eq] at h
  exact (single_inj.mp h).elim And.left (fun hz ↦ (one_ne_zero hz.2).elim)

/-- Twisting by a character and then changing exponents parametrizes algebra isomorphisms of
group algebras whose units are monomials. The character is on the source group. -/
def charTwistDomCongrEquiv :
    ((G →* kˣ) × (G ≃* H)) ≃ (MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k H) :=
  Equiv.ofBijective
    (fun p ↦ (charTwist p.1).trans (domCongr k k p.2)) <| by
      constructor
      · rintro ⟨χ, σ⟩ ⟨ψ, τ⟩ h
        have heval (a : G) :
            (χ a, toUnits (σ a)) = (ψ a, toUnits (τ a)) := by
          apply unitsSingle_injective
          apply Units.ext
          simpa [AlgEquiv.trans_apply] using DFunLike.congr_fun h (single a (1 : k))
        exact Prod.ext (MonoidHom.ext fun a ↦ congrArg Prod.fst (heval a))
          (MulEquiv.ext fun a ↦ toUnits.injective (congrArg Prod.snd (heval a)))
      · intro e
        let σ : G ≃* H :=
          { exponentHom e.toAlgHom with
            invFun := exponentHom e.symm.toAlgHom
            left_inv := exponentHom_leftInverse e
            right_inv := (exponentHom_leftInverse e.symm).rightInverse }
        refine ⟨⟨(MonoidHom.fst _ _).comp (monomialData e.toAlgHom), σ⟩, ?_⟩
        apply AlgEquiv.ext
        have h : ((charTwist ((MonoidHom.fst _ _).comp (monomialData e.toAlgHom))).trans
            (domCongr k k σ)).toAlgHom = e.toAlgHom := by
          refine algHom_ext (fun a ↦ ?_) (Subsingleton.elim ..)
          have hσ : σ a = exponentHom e.toAlgHom a := (rfl)
          simpa [hσ] using (apply_single_eq e.toAlgHom a (1 : k)).symm
        exact AlgHom.congr_fun h

/-- The forward map twists coefficients and then transports exponents. -/
theorem charTwistDomCongrEquiv_apply (p : (G →* kˣ) × (G ≃* H)) :
    charTwistDomCongrEquiv p = (charTwist p.1).trans (domCongr k k p.2) := (rfl)

/-- The algebra isomorphism associated to a character and exponent group isomorphism
acts on a monomial by scaling its coefficient and changing its exponent. -/
@[simp]
theorem charTwistDomCongrEquiv_apply_single (p : (G →* kˣ) × (G ≃* H)) (a : G) (r : k) :
    charTwistDomCongrEquiv p (single a r) = single (p.2 a) ((p.1 a : k) * r) := by
  simp [charTwistDomCongrEquiv_apply]

/-- The two parameters recovered from an algebra isomorphism describe its action on
every monomial. -/
theorem apply_single_eq_charTwistDomCongrEquiv_symm
    (e : MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k H) (a : G) (r : k) :
    e (single a r) = single ((charTwistDomCongrEquiv.symm e).2 a)
      (((charTwistDomCongrEquiv.symm e).1 a : k) * r) := by
  rw [← charTwistDomCongrEquiv_apply_single, Equiv.apply_symm_apply]

/-- The trivial character and the identity exponent map give the identity isomorphism. -/
@[simp]
theorem charTwistDomCongrEquiv_refl :
    charTwistDomCongrEquiv (1, MulEquiv.refl G) =
      (AlgEquiv.refl : MonoidAlgebra k G ≃ₐ[k] MonoidAlgebra k G) := by
  rw [charTwistDomCongrEquiv_apply, Prod.fst, Prod.snd, charTwist_one, domCongr_refl]
  rfl

/-- The second coefficient character is pulled back along the first exponent isomorphism
when composing two group algebra isomorphisms. -/
theorem charTwistDomCongrEquiv_trans {J : Type*} [Group J] [TwoUniqueProds J]
    (p : (G →* kˣ) × (G ≃* H)) (q : (H →* kˣ) × (H ≃* J)) :
    (charTwistDomCongrEquiv p).trans (charTwistDomCongrEquiv q) =
      charTwistDomCongrEquiv (p.1 * q.1.comp p.2.toMonoidHom, p.2.trans q.2) := by
  apply AlgEquiv.ext
  suffices h : ((charTwistDomCongrEquiv p).trans (charTwistDomCongrEquiv q)).toAlgHom =
      (charTwistDomCongrEquiv (p.1 * q.1.comp p.2.toMonoidHom, p.2.trans q.2)).toAlgHom from
    AlgHom.congr_fun h
  refine algHom_ext (fun a ↦ ?_) (Subsingleton.elim ..)
  simp [mul_comm]

/-- The inverse isomorphism uses the inverse exponent map and the inverse character
pulled back along that map. -/
@[simp]
theorem charTwistDomCongrEquiv_symm (p : (G →* kˣ) × (G ≃* H)) :
    (charTwistDomCongrEquiv p).symm =
      charTwistDomCongrEquiv ((p.1.comp p.2.symm.toMonoidHom)⁻¹, p.2.symm) := by
  apply AlgEquiv.ext
  intro a
  apply (charTwistDomCongrEquiv p).injective
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.trans_apply, charTwistDomCongrEquiv_trans]
  have h : (p.1.comp p.2.symm.toMonoidHom)⁻¹ * p.1.comp p.2.symm.toMonoidHom = 1 :=
    MonoidHom.ext fun a ↦ by simp [MonoidHom.mul_apply]
  simp only [h, MulEquiv.symm_trans_self, charTwistDomCongrEquiv_refl]
  rfl

end MonoidAlgebra
