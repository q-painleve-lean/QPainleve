/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel
public import QPainleve.Algebra.Cluster.XMutation.Basic
public import QPainleve.Geometry.Toric.CharacterTorus.BinomialShear
public import QPainleve.Geometry.Toric.CharacterTorus.Evaluation

/-!
# Center mutation and evaluation on the dense tori

The integral charge basis change induces the monomial change of center parameters.
Together with the binomial shear on the surface characters, it gives the elementary
transformation on the joint function field of centers and surface coordinates. Evaluating
a mutated X coordinate using the new charges agrees with mutating the evaluated coordinate.

The surface character formula follows Gross, Hacking and Keel,
*Birational geometry of cluster algebras*, (1.4) and Lemma 3.2.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative
open LinearMap (BilinForm)

namespace QPainleve.Cluster

open CharacterTorus
open scoped Int

universe u

variable {ι N : Type u} [Fintype ι] [DecidableEq ι] [AddCommGroup N]

local notation "A" => (ι → ℤ)
local notation "e" i:arg => (Pi.single i (1 : ℤ) : ι → ℤ)

variable (ω : BilinForm ℤ N) (v : (ι → ℤ) →ₗ[ℤ] N) (p : ι)

local notation "ε" => chargeExchangeMatrix ω v
local notation "B" => chargeMutationEquiv ε p

section Centers

variable (k : Type u) [CommRing k]

/-- Monomial change of the center parameters under mutation at the given label. -/
def centerMutation (E : Matrix ι ι ℤ) (p : ι) : scheme k A ≅ scheme k A :=
  mapIso k (chargeMutationEquiv E p).toAddEquiv

/-- The center isomorphism pulls characters back by the integral mutation basis change. -/
theorem centerMutation_hom (E : Matrix ι ι ℤ) (p : ι) :
    (centerMutation k E p).hom =
      CharacterTorus.map k (chargeMutationEquiv E p).toAddEquiv.toAddMonoidHom := by
  rw [centerMutation, mapIso_hom]

/-- The inverse center isomorphism pulls characters back by the inverse basis change. -/
@[simp]
theorem centerMutation_inv (E : Matrix ι ι ℤ) (p : ι) :
    (centerMutation k E p).inv =
      CharacterTorus.map k (chargeMutationEquiv E p).symm.toAddEquiv.toAddMonoidHom := by
  rw [centerMutation, mapIso_inv]
  rfl

/-- On points, center mutation precomposes the center character with the mutation basis change. -/
@[reassoc (attr := simp)]
theorem pointsEquiv_symm_comp_centerMutation_hom (E : Matrix ι ι ℤ) (p : ι)
    (c : Multiplicative A →* kˣ) :
    ((pointsEquiv k A).symm c).val ≫ (centerMutation k E p).hom =
      ((pointsEquiv k A).symm
        (c.comp (chargeMutationEquiv E p).toAddEquiv.toAddMonoidHom.toMultiplicative)).val := by
  rw [centerMutation_hom, pointsEquiv_symm_comp_map]

/-- The new center coordinate at the pivot is the reciprocal of the old one. -/
theorem centerMutation_character_apply_self (E : Matrix ι ι ℤ) (p : ι)
    (c : Multiplicative A →* kˣ) :
    (c.comp (chargeMutationEquiv E p).toAddEquiv.toAddMonoidHom.toMultiplicative) (ofAdd (e p)) =
      (c (ofAdd (e p)))⁻¹ := by
  simp [AddMonoidHom.coe_toMultiplicative, ofAdd_neg]

/-- A nonpivot center coordinate is multiplied by a power of the pivot center coordinate. -/
theorem centerMutation_character_apply_of_ne (hω : ω.IsAlt)
    (c : Multiplicative A →* kˣ) {i : ι} (hi : i ≠ p) :
    (c.comp (B).toAddEquiv.toAddMonoidHom.toMultiplicative) (ofAdd (e i)) =
      c (ofAdd (e i)) * c (ofAdd (e p)) ^ (ε i p)⁺ := by
  simp only [MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
    toAdd_ofAdd, AddEquiv.coe_toAddMonoidHom, LinearEquiv.coe_toAddEquiv]
  -- Evaluate the additive equivalence through its underlying linear equivalence.
  change c (ofAdd (B (e i))) = _
  rw [chargeMutationEquiv_single_of_ne ε p hi, ofAdd_add, ofAdd_zsmul, map_mul, map_zpow]
  simp only [chargeExchangeMatrix_apply, hω.neg_eq]

end Centers

variable (k : Type u) [Field k]

variable [Module.Free ℤ N]

local notation "Joint" => FunctionField k (A × N)

private def pivotExponent : A × N :=
  (e p, v (e p))

omit [Fintype ι] [Module.Free ℤ N] in
private theorem pivotExponent_ne_zero : pivotExponent v p ≠ 0 := by
  intro h
  have hp := congrFun (congrArg Prod.fst h) p
  simp [pivotExponent] at hp

private def mutationFunctional : (A × N) →+ ℤ :=
  (-(ω.flip (v (e p))).toAddMonoidHom).comp (AddMonoidHom.snd A N)

omit [Fintype ι] [Module.Free ℤ N] in
private theorem mutationFunctional_apply (a : A × N) :
    mutationFunctional ω v p a = -ω a.2 (v (e p)) :=
  (rfl)

omit [Fintype ι] [Module.Free ℤ N] in
private theorem mutationFunctional_pivot (hω : ω.IsAlt) :
    mutationFunctional ω v p (pivotExponent v p) = 0 := by
  simp [mutationFunctional_apply, pivotExponent, hω.self_eq_zero]

/-- Joint pullback for the monomial center change and the binomial transformation of surface
characters. Center and surface coordinates are both independent in the source field. -/
def centerMutationPullback (hω : ω.IsAlt) : Joint ≃ₐ[k] Joint :=
  (functionFieldEquiv k ((B).prodCongr (LinearEquiv.refl ℤ N)).toAddEquiv).trans
    (binomialShear k (pivotExponent v p) (one_add_monomial_ne_zero k (pivotExponent_ne_zero v p))
      (mutationFunctional ω v p) (mutationFunctional_pivot ω v p hω))

/-- The joint pullback acts on a center exponent by the basis change and on a surface exponent
by its binomial factor. -/
@[simp]
theorem centerMutationPullback_monomial (hω : ω.IsAlt) (a : A) (h : N) :
    centerMutationPullback ω v p k hω (monomial k (ofAdd (a, h))) =
      monomial k (ofAdd (B a, h)) *
        (1 + monomial k (ofAdd (e p, v (e p)))) ^ (-ω h (v (e p))) := by
  have he (r : (A × N) ≃+ (A × N)) :
      functionFieldEquiv k r (monomial k (ofAdd (a, h))) = monomial k (ofAdd (r (a, h))) := by
    rw [← AlgEquiv.toAlgHom_apply, functionFieldEquiv_toAlgHom, functionFieldMap_monomial,
      AddEquiv.coe_toAddMonoidHom]
  simp [centerMutationPullback, he, mutationFunctional_apply, pivotExponent]

local notation "r" => Finsupp.linearEquivFunOnFinite ℤ ℤ ι

private def xEvaluationGraph : (ι →₀ ℤ) →+ (A × N) :=
  (r).toAddEquiv.toAddMonoidHom.prod (v.toAddMonoidHom.comp (r).toAddEquiv.toAddMonoidHom)

omit [DecidableEq ι] [Module.Free ℤ N] in
private theorem xEvaluationGraph_injective : Function.Injective (xEvaluationGraph v) :=
  fun _ _ h ↦ (r).injective (congrArg Prod.fst h)

omit [DecidableEq ι] in
/-- Pullback of an independent X function to the joint field of variable centers and surface
coordinates. The standard finite basis identifies the X exponent lattice with the finitely
supported exponents used by the X mutation API. -/
def xEvaluationPullback : FunctionField k (ι →₀ ℤ) →ₐ[k] Joint :=
  functionFieldMap k (xEvaluationGraph v) (xEvaluationGraph_injective v)

omit [DecidableEq ι] in
/-- The X evaluation pullback agrees on every monomial with the rational pullback of the
torus evaluation morphism after identifying the respective exponent lattices. -/
@[simp]
theorem xEvaluationPullback_monomial (a : ι →₀ ℤ) :
    xEvaluationPullback v k (monomial k (ofAdd a)) =
      rationalPullback k (CharacterTorus.evaluation k v.toAddMonoidHom).toRationalMap
        (monomial k (ofAdd (r a))) := by
  rw [xEvaluationPullback, functionFieldMap_monomial, rationalPullback_evaluation_monomial]
  rfl

/-- Evaluation of an independent X coordinate is the product of the matching center
coordinate and charge monomial. -/
@[simp]
theorem xEvaluationPullback_xCoordinate (i : ι) :
    xEvaluationPullback v k (xCoordinate k i) = monomial k (ofAdd (e i, v (e i))) := by
  simp [xCoordinate_def, ← monomial_ofAdd]

private theorem centerMutationPullback_xEvaluation_of_ne (hω : ω.IsAlt) {i : ι} (hi : i ≠ p) :
    centerMutationPullback ω v p k hω
      (xEvaluationPullback (chargeMutation ω v p) k (xCoordinate k i)) =
    xEvaluationPullback v k (xMutation k p (fun j ↦ ε j p) (xCoordinate k i)) := by
  let a := (ε i p)⁺
  have hb : B (e i) = e i + a • e p := by
    simpa only [a, chargeExchangeMatrix_apply, hω.neg_eq] using
      chargeMutationEquiv_single_of_ne ε p hi
  have hv : chargeMutation ω v p (e i) = v (e i) + a • v (e p) := by
    rw [chargeMutation_apply, hb, map_add, map_smul]
  have hdet : ω (chargeMutation ω v p (e i)) (v (e p)) = ε i p := by
    rw [hv, BilinForm.add_left, BilinForm.smul_left, hω.self_eq_zero, mul_zero, add_zero,
      chargeExchangeMatrix_apply]
  rw [xMutation_apply_of_ne _ _ _ hi]
  simp only [map_mul, map_zpow₀, map_add, map_one, xEvaluationPullback_xCoordinate,
    centerMutationPullback_monomial]
  rw [hdet, hb, hv]
  have he : (e i + a • e p, v (e i) + a • v (e p)) =
      (e i, v (e i)) + a • (e p, v (e p)) := rfl
  rw [he, ofAdd_add, map_mul, ofAdd_zsmul, map_zpow]
  rfl

/-- Joint evaluation commutes with X mutation. The equality is in the function field with
variable centers, and uses the mutated charge map at the target. -/
theorem centerMutationPullback_comp_xEvaluationPullback (hω : ω.IsAlt) :
    (centerMutationPullback ω v p k hω).toAlgHom.comp
        (xEvaluationPullback (chargeMutation ω v p) k) =
      (xEvaluationPullback v k).comp (xMutation k p (fun j ↦ ε j p)).toAlgHom := by
  apply functionField_hom_ext_basis (Finsupp.basisSingleOne (R := ℤ) (ι := ι))
  intro i
  rw [Finsupp.coe_basisSingleOne, monomial_ofAdd]
  simp only [← xCoordinate_def, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
  by_cases hi : i = p
  · subst i
    rw [xMutation_apply_self, map_inv₀, xEvaluationPullback_xCoordinate,
      xEvaluationPullback_xCoordinate, centerMutationPullback_monomial,
      chargeMutationEquiv_single_self, chargeMutation_single_self,
      BilinForm.neg_left, hω.self_eq_zero]
    simp only [neg_zero, zpow_zero, mul_one]
    have hneg : (-(e p), -v (e p)) = -(e p, v (e p)) := rfl
    rw [hneg, ofAdd_neg, map_inv]
  · exact centerMutationPullback_xEvaluation_of_ne ω v p k hω hi

end QPainleve.Cluster
