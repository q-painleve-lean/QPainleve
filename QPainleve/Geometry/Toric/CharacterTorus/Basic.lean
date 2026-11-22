/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import QPainleve.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Character tori and their function fields

The additive group algebra of the character lattice is the coordinate ring of a split torus.
A lattice basis identifies it with a Laurent polynomial algebra, with exponents given by the
basis coordinates. Monomials and pullbacks on the function field are defined intrinsically.
For a lattice equivalence, `AddMonoidAlgebra.domCongr` and
`IsFractionRing.algEquivOfAlgEquiv` give the corresponding function field equivalence.
-/

public noncomputable section

namespace QPainleve.CharacterTorus

/-- The multivariate Laurent polynomial algebra with finitely supported integer exponents. -/
abbrev LaurentPolynomials (k : Type*) (ι : Type*) [CommSemiring k] :=
  AddMonoidAlgebra k (ι →₀ ℤ)

end QPainleve.CharacterTorus

namespace Module.Basis

universe u v w

variable {k : Type u} {B : Type v} {ι : Type w} [CommSemiring k] [AddCommGroup B] [Module ℤ B]

/-- The algebra of lattice characters in the Laurent coordinates of an integral basis. -/
def laurentPolynomialEquiv (b : Module.Basis ι ℤ B) :
    AddMonoidAlgebra k B ≃ₐ[k] QPainleve.CharacterTorus.LaurentPolynomials k ι :=
  AddMonoidAlgebra.domCongr k k b.repr.toAddEquiv

@[simp]
theorem laurentPolynomialEquiv_single (b : Module.Basis ι ℤ B) (x : B) (r : k) :
    b.laurentPolynomialEquiv (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single (b.repr x) r :=
  AddMonoidAlgebra.domCongr_single b.repr.toAddEquiv x r

@[simp]
theorem laurentPolynomialEquiv_symm_single (b : Module.Basis ι ℤ B) (x : ι →₀ ℤ) (r : k) :
    b.laurentPolynomialEquiv.symm (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single (b.repr.symm x) r := by
  apply b.laurentPolynomialEquiv.injective
  simp

/-- Transporting the lattice and its basis together leaves Laurent coordinates unchanged. -/
theorem laurentPolynomialEquiv_map {C : Type*} [AddCommGroup C] [Module ℤ C]
    (b : Module.Basis ι ℤ B) (e : B ≃ₗ[ℤ] C) :
    (AddMonoidAlgebra.domCongr k k e.toAddEquiv).trans (b.map e).laurentPolynomialEquiv =
      b.laurentPolynomialEquiv := by
  simp only [laurentPolynomialEquiv, AddMonoidAlgebra.trans_domCongr_domCongr]
  congr 1
  ext x
  simp [Module.Basis.map_repr]

end Module.Basis

namespace QPainleve.CharacterTorus

universe u v w

variable (k : Type u) (B : Type v) {C : Type w}

/-- The fraction ring of the character algebra. For a free abelian lattice this is the function
field of the character torus. -/
abbrev FunctionField [Field k] [AddCommGroup B] := FractionRing (AddMonoidAlgebra k B)

variable {B} [Field k] [AddCommGroup B]

/-- The rational function given by the character with exponent `x`, as a multiplicative map. -/
def monomial : Multiplicative B →* FunctionField k B :=
  (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)).toMonoidHom.comp
    (AddMonoidAlgebra.of k B)

theorem monomial_ofAdd (x : B) :
    monomial k (Multiplicative.ofAdd x) =
      algebraMap (AddMonoidAlgebra k B) (FunctionField k B) (AddMonoidAlgebra.single x 1) := (rfl)

/-- The distinct character monomials form a linearly independent family in the function field. -/
theorem linearIndependent_monomial :
    LinearIndependent k (fun x : B ↦ monomial k (Multiplicative.ofAdd x)) := by
  let f : AddMonoidAlgebra k B →ₗ[k] FunctionField k B :=
    (IsScalarTower.toAlgHom k _ _).toLinearMap
  have h : (fun x : B ↦ monomial k (Multiplicative.ofAdd x)) =
      f ∘ AddMonoidAlgebra.basis B k := by
    funext x
    simp only [f, Function.comp_apply, AddMonoidAlgebra.basis_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', monomial_ofAdd]
  rw [h]
  exact (AddMonoidAlgebra.basis B k).linearIndependent.map' f
    (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective _ _))

@[simp]
theorem monomial_ne_zero (x : B) :
    monomial k (Multiplicative.ofAdd x) ≠ (0 : FunctionField k B) := by
  rw [← map_zero (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)), monomial_ofAdd]
  exact (IsFractionRing.injective _ _).ne (by simp)

/-- The binomial used in a cluster mutation is nonzero for every nonzero character exponent. -/
theorem one_add_monomial_ne_zero {x : B} (hx : x ≠ 0) :
    1 + monomial k (Multiplicative.ofAdd x) ≠ 0 := by
  rw [monomial_ofAdd, ← map_one (algebraMap (AddMonoidAlgebra k B) (FunctionField k B)),
    ← map_add, ← map_zero (algebraMap (AddMonoidAlgebra k B) (FunctionField k B))]
  intro h
  have hcoeff := congrArg (fun p : AddMonoidAlgebra k B ↦ p.coeff x)
    (IsFractionRing.injective (AddMonoidAlgebra k B) (FunctionField k B) h)
  simp [AddMonoidAlgebra.one_def, hx] at hcoeff

section Free

variable {k} [Module ℤ B] [Module.Free ℤ B]

/-- Algebra maps out of the torus function field are determined by their values on characters. -/
theorem functionField_hom_ext {K : Type*} [Field K] [Algebra k K]
    {f g : FunctionField k B →ₐ[k] K}
    (h : ∀ x : B, f (monomial k (Multiplicative.ofAdd x)) =
      g (monomial k (Multiplicative.ofAdd x))) : f = g := by
  apply AlgHom.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := AddMonoidAlgebra k B)
  have hAlg : f.comp (IsScalarTower.toAlgHom k (AddMonoidAlgebra k B) (FunctionField k B)) =
      g.comp (IsScalarTower.toAlgHom k (AddMonoidAlgebra k B) (FunctionField k B)) := by
    apply (AddMonoidAlgebra.lift k K B).symm.injective
    apply MonoidHom.ext
    intro x
    simpa only [AddMonoidAlgebra.lift_symm_apply, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', monomial_ofAdd] using h x.toAdd
  exact fun z ↦ AlgHom.congr_fun hAlg z

omit [Module.Free ℤ B] in
/-- The monomials of any integral basis determine a map out of the torus function field. -/
theorem functionField_hom_ext_basis {ι K : Type*} [Field K] [Algebra k K]
    (b : Module.Basis ι ℤ B) {f g : FunctionField k B →ₐ[k] K}
    (h : ∀ i, f (monomial k (Multiplicative.ofAdd (b i))) =
      g (monomial k (Multiplicative.ofAdd (b i)))) : f = g := by
  obtain rfl : ‹Module ℤ B› = AddCommGroup.toIntModule B := Subsingleton.elim _ _
  let : Module.Free ℤ B := Module.Free.of_basis b
  apply functionField_hom_ext
  let pullCharacter (φ : FunctionField k B →ₐ[k] K) : B →ₗ[ℤ] Additive Kˣ :=
    let χ := ((φ : FunctionField k B →* K).comp (monomial k)).toHomUnits.toAdditiveRight
    χ.toIntLinearMap
  have hBasis (i : ι) : pullCharacter f (b i) = pullCharacter g (b i) := Units.ext (h i)
  intro x
  exact congrArg (fun a : Additive Kˣ ↦ (a.toMul : K)) (LinearMap.congr_fun (b.ext hBasis) x)

variable (k) [AddCommGroup C] [Module ℤ C] [Module.Free ℤ C]

omit [Module ℤ B] [Module.Free ℤ B] [Module ℤ C] [Module.Free ℤ C] in
private theorem injective_monomialLift (f : B →+ C) (hf : Function.Injective f) :
    Function.Injective ((IsScalarTower.toAlgHom k (AddMonoidAlgebra k C) (FunctionField k C)).comp
      (AddMonoidAlgebra.mapDomainAlgHom k k f)) :=
  (IsFractionRing.injective _ _).comp (AddMonoidAlgebra.mapDomain_injective hf)

/-- An injective lattice map pulls rational functions back by transporting their exponents. -/
def functionFieldMap (f : B →+ C) (hf : Function.Injective f) :
    FunctionField k B →ₐ[k] FunctionField k C :=
  IsFractionRing.liftAlgHom (injective_monomialLift k f hf)

/-- The fraction-field map extends transport of exponents on the whole coordinate ring. -/
@[simp]
theorem functionFieldMap_algebraMap (f : B →+ C) (hf : Function.Injective f)
    (p : AddMonoidAlgebra k B) :
    functionFieldMap k f hf (algebraMap (AddMonoidAlgebra k B) (FunctionField k B) p) =
      algebraMap (AddMonoidAlgebra k C) (FunctionField k C)
        (AddMonoidAlgebra.mapDomainAlgHom k k f p) := by
  rw [functionFieldMap, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

@[simp]
theorem functionFieldMap_monomial (f : B →+ C) (hf : Function.Injective f) (x : B) :
    functionFieldMap k f hf (monomial k (Multiplicative.ofAdd x)) =
      monomial k (Multiplicative.ofAdd (f x)) := by
  simp [monomial_ofAdd]

@[simp]
theorem functionFieldMap_id :
    functionFieldMap k (AddMonoidHom.id B) Function.injective_id = AlgHom.id k _ := by
  apply functionField_hom_ext
  simp

theorem functionFieldMap_comp {D : Type*} [AddCommGroup D] [Module ℤ D] [Module.Free ℤ D]
    (f : B →+ C) (g : C →+ D) (hf : Function.Injective f) (hg : Function.Injective g) :
    functionFieldMap k (g.comp f) (hg.comp hf) =
      (functionFieldMap k g hg).comp (functionFieldMap k f hf) := by
  apply functionField_hom_ext
  simp

/-- The fraction ring equivalence induced by a lattice equivalence acts by the pullback
along its underlying additive homomorphism. -/
@[simp]
theorem algEquivOfAlgEquiv_domCongr_toAlgHom (e : B ≃+ C) :
    (IsFractionRing.algEquivOfAlgEquiv (AddMonoidAlgebra.domCongr k k e) :
      FunctionField k B ≃ₐ[k] FunctionField k C).toAlgHom =
      functionFieldMap k e.toAddMonoidHom
        (by simpa only [AddEquiv.coe_toAddMonoidHom] using e.injective) := by
  apply functionField_hom_ext
  intro x
  rw [AlgEquiv.toAlgHom_apply, functionFieldMap_monomial]
  simp [monomial_ofAdd]

end Free

end QPainleve.CharacterTorus
