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

/-- A finitely generated character lattice gives a scheme locally of finite type over the base. -/
instance {k B : Type u} [CommRing k] [AddCommGroup B] [Module ℤ B] [Module.Finite ℤ B] :
    LocallyOfFiniteType (scheme k B ↘ Spec (CommRingCat.of k)) := by
  have h : (inferInstance : Module ℤ B) = AddCommGroup.toIntModule B := Subsingleton.elim _ _
  have : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp (h ▸ ‹Module.Finite ℤ B›)
  have : AddMonoid.FG B := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  exact AlgebraicGeometry.locallyOfFiniteType_specOverSpec

variable (k : Type u) [Field k]
  {B C D : Type u} [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
  [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C]
  [Module ℤ D] [Module.Free ℤ D]

local instance {G : Type*} [AddCommGroup G] [Module ℤ G] [Module.Free ℤ G] : HasUniqueDiv G :=
  .of_isTorsionFree ℤ G

/-- The identity rational map of a character torus pulls back each rational function to itself. -/
@[simp]
theorem rationalPullback_id :
    rationalPullback k (Scheme.RationalMap.id (scheme k B)) = RingHom.id _ := by
  ext a
  simp [rationalPullback_apply]

/-- Pullbacks of rational maps between character tori compose in the reverse order. -/
@[simp]
theorem rationalPullback_comp (f : (scheme k D) ⤏ (scheme k C))
    (g : (scheme k C) ⤏ (scheme k B)) [f.IsDominant] [g.IsDominant] :
    rationalPullback k (f.comp g) = (rationalPullback k f).comp (rationalPullback k g) := by
  ext a
  simp [rationalPullback_apply]

variable (B) in
/-- The character field and the generic stalk of the character scheme are canonically
isomorphic over the base field. -/
def fractionRingAlgEquiv : FunctionField k B ≃ₐ[k] (scheme k B).functionField :=
  AlgEquiv.ofRingEquiv (f := fractionRingEquiv k B) fun a ↦ by
    have h := DFunLike.congr_fun
      (rationalPullback_comp_algebraMap (Scheme.RationalMap.id (scheme k B)))
      (algebraMap k (AddMonoidAlgebra k B) a)
    simp only [rationalPullback_id, RingHom.comp_apply, RingHom.id_apply,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id,
      ← IsScalarTower.algebraMap_apply] at h
    apply (fractionRingEquiv k B).symm.injective
    rw [RingEquiv.symm_apply_apply, h]
    have hBase := congrArg Spec.preimage
      (Scheme.fromSpecStalk_genericPoint_comp_over k (scheme k B))
    rw [specOverSpec_over, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at hBase
    exact congrArg (fractionRingEquiv k B).symm (ConcreteCategory.congr_hom hBase a)

@[simp]
theorem fractionRingAlgEquiv_toRingEquiv :
    (fractionRingAlgEquiv k B).toRingEquiv = fractionRingEquiv k B := (rfl)

variable [Module.Finite ℤ B]

/-- Dominant rational maps of split character tori over the base field are determined by, and
realize, the algebra homomorphisms of their character fields. -/
def rationalPullbackEquiv :
    { f : (scheme k C) ⤏ (scheme k B) //
      f.IsDominant ∧ f.IsOver (Spec (CommRingCat.of k)) } ≃
      (FunctionField k B →ₐ[k] FunctionField k C) :=
  (Scheme.RationalMap.equivFunctionFieldAlgHom k).trans
    (AlgEquiv.arrowCongr (fractionRingAlgEquiv k B).symm (fractionRingAlgEquiv k C).symm)

/-- The correspondence on character fields agrees with the pullback on rational functions. -/
@[simp]
theorem rationalPullbackEquiv_apply (f : (scheme k C) ⤏ (scheme k B)) [f.IsDominant]
    [f.IsOver (Spec (CommRingCat.of k))] :
    ↑(rationalPullbackEquiv k ⟨f, inferInstance, inferInstance⟩) =
      rationalPullback k f := by
  ext a
  rw [rationalPullbackEquiv, Equiv.trans_apply, Scheme.RationalMap.equivFunctionFieldAlgHom_apply,
    rationalPullback_apply]
  simp [AlgEquiv.arrowCongr, ← AlgEquiv.coe_toRingEquiv]

/-- The rational map associated with a homomorphism pulls back by that homomorphism. -/
@[simp]
theorem rationalPullback_rationalPullbackEquiv_symm
    (φ : FunctionField k B →ₐ[k] FunctionField k C) :
    let f := (rationalPullbackEquiv k).symm φ
    letI := f.2.1
    rationalPullback k f.1 = φ.toRingHom := by
  let f := (rationalPullbackEquiv k).symm φ
  have := f.2.1
  have := f.2.2
  exact (rationalPullbackEquiv_apply k f.1).symm.trans
    (congrArg AlgHom.toRingHom ((rationalPullbackEquiv k).apply_symm_apply φ))

/-- The composition of the rational maps induced by a character field equivalence and its
inverse is the identity. -/
@[simp]
theorem rationalPullbackEquiv_symm_comp_symm [Module.Finite ℤ C]
    (e : FunctionField k B ≃ₐ[k] FunctionField k C) :
    let f := (rationalPullbackEquiv k).symm e.toAlgHom
    let g := (rationalPullbackEquiv k).symm e.symm.toAlgHom
    letI := f.2.1
    f.1.comp g.1 = Scheme.RationalMap.id (scheme k C) := by
  let f := (rationalPullbackEquiv k).symm e.toAlgHom
  let g := (rationalPullbackEquiv k).symm e.symm.toAlgHom
  have := f.2.1
  have := g.2.1
  apply (rationalPullback_eq_iff _ _).mp
  rw [rationalPullback_comp, rationalPullback_id]
  rw [rationalPullback_rationalPullbackEquiv_symm, rationalPullback_rationalPullbackEquiv_symm]
  ext a
  exact e.apply_symm_apply a

end QPainleve.CharacterTorus
