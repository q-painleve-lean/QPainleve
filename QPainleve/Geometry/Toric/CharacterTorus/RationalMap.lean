/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Pullback
public import QPainleve.Geometry.Toric.CharacterTorus.Scheme

/-!
# Rational maps of character tori

Dominant rational maps of split character tori over the base field correspond to algebra
homomorphisms of the fraction fields of their character rings. In particular an algebra
equivalence of character fields gives mutually inverse scheme rational maps.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace QPainleve.CharacterTorus

universe u

variable (k : Type u) [Field k]
  {B C : Type u} [AddCommGroup B] [AddCommGroup C]
  [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C]

attribute [local instance] hasUniqueDiv_of_free_int

variable [Module.Finite ℤ B]

/-- Dominant rational maps of split character tori over the base field are determined by, and
realize, the algebra homomorphisms of their character fields. -/
def rationalPullbackEquiv :
    { f : (scheme k C) ⤏ (scheme k B) //
      f.IsDominant ∧ f.IsOver (scheme k C ↘ Spec (.of k)) (scheme k B ↘ Spec (.of k)) } ≃
      (FunctionField k B →ₐ[k] FunctionField k C) :=
  (Scheme.RationalMap.equivFunctionFieldAlgHom k).trans
    (AlgEquiv.arrowCongr (affineFractionRingAlgEquiv k B).symm
      (affineFractionRingAlgEquiv k C).symm)

/-- The correspondence on character fields agrees with the pullback on rational functions. -/
@[simp]
theorem rationalPullbackEquiv_apply (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant]
    [f.IsOver (scheme k C ↘ Spec (.of k)) (scheme k B ↘ Spec (.of k))] :
    ↑(rationalPullbackEquiv k ⟨f, inferInstance, inferInstance⟩) =
      affineRationalPullback k f := by
  ext a
  rw [rationalPullbackEquiv, Equiv.trans_apply, Scheme.RationalMap.equivFunctionFieldAlgHom_apply,
    affineRationalPullback_apply]
  simp [AlgEquiv.arrowCongr, ← AlgEquiv.coe_toRingEquiv]

/-- The rational map associated with a homomorphism pulls back by that homomorphism. -/
@[simp]
theorem affineRationalPullback_rationalPullbackEquiv_symm
    (φ : FunctionField k B →ₐ[k] FunctionField k C) :
    let f := (rationalPullbackEquiv k).symm φ
    letI := f.property.left
    affineRationalPullback k f.val = φ.toRingHom := by
  let f := (rationalPullbackEquiv k).symm φ
  have := f.property.left
  have := f.property.right
  exact (rationalPullbackEquiv_apply k f.val).symm.trans
    (congrArg AlgHom.toRingHom ((rationalPullbackEquiv k).apply_symm_apply φ))

/-- The composition of the rational maps induced by a character field equivalence and its
inverse is the identity. -/
@[simp]
theorem rationalPullbackEquiv_symm_comp_symm [Module.Finite ℤ C]
    (e : FunctionField k B ≃ₐ[k] FunctionField k C) :
    let f := (rationalPullbackEquiv k).symm e.toAlgHom
    let g := (rationalPullbackEquiv k).symm e.symm.toAlgHom
    letI := f.property.left
    f.val.comp g.val = Scheme.RationalMap.id (scheme k C) := by
  let f := (rationalPullbackEquiv k).symm e.toAlgHom
  let g := (rationalPullbackEquiv k).symm e.symm.toAlgHom
  have := f.property.left
  have := g.property.left
  apply (affineRationalPullback_eq_iff _ _).mp
  rw [affineRationalPullback_comp, affineRationalPullback_id]
  rw [affineRationalPullback_rationalPullbackEquiv_symm,
    affineRationalPullback_rationalPullbackEquiv_symm]
  ext a
  exact e.apply_symm_apply a

end QPainleve.CharacterTorus
