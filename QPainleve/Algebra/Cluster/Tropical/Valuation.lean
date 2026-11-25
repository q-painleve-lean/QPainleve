/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.Algebra.MonoidAlgebra.Valuation

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import QPainleve.Algebra.Cluster.XMutation.Monomial
import QPainleve.RingTheory.Valuation.WithTop

/-!
# Tropical transport of coordinate valuations

A tuple of weights defines a monomial valuation on the field of independent
cluster X coordinates. Pullback along a word transports it by the tropical
word. This uses the open mutation chart and works in every characteristic.
-/

public noncomputable section

open CategoryTheory Quiver TauCeti LaurentRing AddMonoidAlgebra

namespace QPainleve.Cluster

variable (k : Type*) [Field k] {ι Γ : Type*}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

local notation "R" => LaurentRing k ι
local notation "K" => FractionRing R
local notation "inK" => algebraMap R K
local notation "weight" b => LinearMap.toAddMonoidHom (Finsupp.linearCombination ℤ b)

/-- Assign the given weight to each independent X coordinate and take the
minimum monomial weight on Laurent polynomials. -/
def xAddValuation (b : ι → Γ) : AddValuation K (WithTop Γ) :=
  monomialAddValuation (weight b)

variable {k}

/-- The value of a Laurent polynomial is the minimum of the weighted degrees
of its nonzero terms. -/
theorem xAddValuation_algebraMap (b : ι → Γ) (p : R) :
    xAddValuation k b (inK p) =
      p.coeff.support.inf fun a => (Finsupp.linearCombination ℤ b a : WithTop Γ) :=
  monomialAddValuation_algebraMap (weight b) p

/-- The value of an independent coordinate is its assigned weight. -/
@[simp]
theorem xAddValuation_xCoordinate (b : ι → Γ) (i : ι) :
    xAddValuation k b (xCoordinate k i) = b i := by
  simp [xAddValuation, xCoordinate_def, Finsupp.linearCombination_single]

/-- The pivot binomial has weight `min 0 (b i)`, including when its two terms
have the same weight. -/
@[simp]
theorem xAddValuation_one_add_xCoordinate (b : ι → Γ) (i : ι) :
    xAddValuation k b (1 + xCoordinate k i) = (min 0 (b i) : Γ) := by
  classical
  have hi : Finsupp.single i (1 : ℤ) ≠ 0 := by simp
  rw [← map_one inK, xCoordinate_def, ← map_add, xAddValuation_algebraMap,
    one_def, coeff_add, coeff_single, coeff_single,
    Finsupp.support_add_eq (by simp [Ne.symm hi])]
  simp [Finsupp.linearCombination_single]

private theorem value_single_of_coordinate_values (v : AddValuation K (WithTop Γ)) (b : ι → Γ)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 0)
    (hcoord : ∀ i, v (xCoordinate k i) = b i) (a : ι →₀ ℤ) {c : k} (hc : c ≠ 0) :
    v (inK (single a c)) = (weight b) a := by
  have hmon (x : ι →₀ ℤ) : v (inK (single x 1)) = (weight b) x := by
    induction x using Finsupp.induction_linear with
    | zero => simp [← one_def]
    | add x y hx hy =>
      rw [← mul_one (1 : k), ← single_mul_single, map_mul, v.map_mul, hx, hy, map_add,
        WithTop.coe_add]
    | single i n =>
      rw [← CharacterTorus.monomial_ofAdd, monomial_finsupp_single]
      simpa [Finsupp.linearCombination_single] using v.map_zpow_of_eq_coe (hcoord i) n
  have h : single a c = algebraMap k R c * single a 1 := by simp [coe_algebraMap]
  rw [h, map_mul, v.map_mul, ← IsScalarTower.algebraMap_apply, hconst c hc, hmon, zero_add]

private theorem value_algebraMap_le (v : AddValuation K (WithTop Γ)) (b : ι → Γ)
    (hconst : ∀ c : k, c ≠ 0 → v (algebraMap k K c) = 0)
    (hcoord : ∀ i, v (xCoordinate k i) = b i) (p : R) :
    xAddValuation k b (inK p) ≤ v (inK p) := by
  rw [xAddValuation_algebraMap]
  calc
    _ ≤ v (∑ a ∈ p.coeff.support, inK (single a (p.coeff a))) :=
      v.map_le_sum fun a ha => by
        rw [value_single_of_coordinate_values v b hconst hcoord a
          (Finsupp.mem_support_iff.mp ha)]
        exact Finset.inf_le ha
    _ = _ := by rw [← map_sum, ← Finsupp.sum, sum_coeff_single]

/-- A nonzero coefficient has weight zero. -/
@[simp]
theorem xAddValuation_algebraMap_const (b : ι → Γ) {c : k} (hc : c ≠ 0) :
    xAddValuation k b (algebraMap k K c) = 0 := by
  rw [IsScalarTower.algebraMap_apply k R K, xAddValuation]
  have h : algebraMap k R c = single 0 c := by simp [coe_algebraMap]
  rw [h, monomialAddValuation_single _ _ hc]
  simp

variable [DecidableEq ι]

private theorem xAddValuation_xMutation_coordinate (B : SkewExchangeMatrix ι)
    (b : ι → Γ) (p i : ι) :
    xAddValuation k b (xMutation k p (fun j => B.matrix j p) (xCoordinate k i)) =
      (Generator.mutate p).tropical B b i := by
  by_cases hi : i = p
  · subst i
    simp [Generator.tropical_mutate_self]
  · rw [xMutation_apply_of_ne _ _ _ hi, Generator.tropical_mutate_of_ne_smul B b hi,
      (xAddValuation k b).map_mul, (xAddValuation k b).map_mul,
      AddValuation.map_zpow_of_eq_coe _ (xAddValuation_xCoordinate b p),
      AddValuation.map_zpow_of_eq_coe _ (xAddValuation_one_add_xCoordinate b p)]
    simp [posPart_def, sub_eq_add_neg]

private theorem xAddValuation_xMutation_binomial (B : SkewExchangeMatrix ι) (b : ι → Γ)
    (p : ι) :
    xAddValuation k b (xMutation k p (fun j => B.matrix j p) (1 + xCoordinate k p)) =
      xAddValuation k ((Generator.mutate p).tropical B b) (1 + xCoordinate k p) := by
  have hx : xCoordinate k p ≠ 0 := xCoordinate_ne_zero k p
  have h : 1 + (xCoordinate k p)⁻¹ = (1 + xCoordinate k p) * (xCoordinate k p)⁻¹ := by
    simp [add_mul, hx, add_comm]
  simp only [map_add, map_one, xMutation_apply_self, h, AddValuation.map_mul, AddValuation.map_inv,
    xAddValuation_one_add_xCoordinate, xAddValuation_xCoordinate,
    Generator.tropical_mutate_self, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
  rw [← min_add_add_right]
  simp [min_comm]

private theorem xAddValuation_le_xMutation_chart (B : SkewExchangeMatrix ι) (b : ι → Γ)
    (p : ι) (x : XMutationChart k p) :
    xAddValuation k ((Generator.mutate p).tropical B b) (xMutationChartToFunctionField k p x) ≤
      xAddValuation k b (xMutation k p (fun j => B.matrix j p)
        (xMutationChartToFunctionField k p x)) := by
  let e := xMutation k p (fun j => B.matrix j p)
  let v := xAddValuation k b
  let v' := xAddValuation k ((Generator.mutate p).tropical B b)
  let z := 1 + xCoordinate k p
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (1 + (X p : R)) x
  have hx : xMutationChartToFunctionField k p x * z ^ n = inK a := by
    simpa [z, xCoordinate_def, X_def] using congrArg (xMutationChartToFunctionField k p) ha
  have hpoly := value_algebraMap_le (v.comap e.toRingHom) ((Generator.mutate p).tropical B b)
    (fun c hc => by
      -- The mutation is a k-algebra automorphism, so it fixes constants.
      change v (e (algebraMap k K c)) = 0
      rw [e.commutes]
      exact xAddValuation_algebraMap_const b hc)
    (xAddValuation_xMutation_coordinate B b p) a
  -- Expand the pulled-back valuation at the cleared numerator.
  change v' (inK a) ≤ v (e (inK a)) at hpoly
  rw [← hx, map_mul e, map_pow e, v'.map_mul, v.map_mul, v.map_pow] at hpoly
  have hz : v (e z) = v' z := xAddValuation_xMutation_binomial B b p
  rw [hz, ← v'.map_pow] at hpoly
  exact (WithTop.add_le_add_iff_right
    ((v'.ne_top_iff).2 (pow_ne_zero n (one_add_xCoordinate_ne_zero k p)))).mp hpoly

private theorem xAddValuation_xMutation_algebraMap (B : SkewExchangeMatrix ι) (b : ι → Γ)
    (p : ι) (a : R) :
    xAddValuation k b (xMutation k p (fun j => B.matrix j p) (inK a)) =
      xAddValuation k ((Generator.mutate p).tropical B b) (inK a) := by
  let t := algebraMap R (XMutationChart k p) a
  let e := xMutationChartEquiv k p (fun j => B.matrix j p)
  -- Apply the same chart bound to the inverse change of coordinates.
  have hforward := xAddValuation_le_xMutation_chart B b p t
  have hreverse := xAddValuation_le_xMutation_chart (B.mutate p)
    ((Generator.mutate p).tropical B b) p (e t)
  have hinv := xMutation_symm_matrixMutation k p B.matrix
  have hb : (Generator.mutate p).tropical (B.mutate p) ((Generator.mutate p).tropical B b) = b :=
    by simpa using Generator.reverse_tropical_tropical (Generator.mutate p) B b
  rw [hb, ← xMutation_xMutationChartToFunctionField] at hreverse
  rw [SkewExchangeMatrix.mutate_matrix, ← hinv,
    AlgEquiv.symm_apply_apply, xMutationChartToFunctionField_algebraMap] at hreverse
  simp only [t, xMutationChartToFunctionField_algebraMap] at hforward
  exact hreverse.antisymm hforward

private theorem xAddValuation_xMutation (B : SkewExchangeMatrix ι) (b : ι → Γ)
    (p : ι) (f : K) :
    xAddValuation k b (xMutation k p (fun j => B.matrix j p) f) =
      xAddValuation k ((Generator.mutate p).tropical B b) f := by
  obtain ⟨a, d, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) f
  simp [IsFractionRing.mk'_eq_div, xAddValuation_xMutation_algebraMap B b p]

/-- Pulling back a coordinate valuation along a generator applies tropical mutation,
relabeling, or inversion to its weights. -/
theorem Generator.xAddValuation_xPullback (g : Generator ι) (B : SkewExchangeMatrix ι)
    (b : ι → Γ) (f : K) :
    xAddValuation k b (g.xPullback k B f) = xAddValuation k (g.tropical B b) f := by
  cases g with
  | mutate p => rw [Generator.xPullback_mutate, xAddValuation_xMutation]
  | permute σ =>
    rw [Generator.xPullback_permute, xReindex]
    rw [xAddValuation, xAddValuation, monomialAddValuation_domCongr]
    apply congrArg (fun w => monomialAddValuation (k := k) w f)
    apply Finsupp.addHom_ext'
    intro i
    ext
    simp [Finsupp.linearCombination_single]
  | invert =>
    rw [Generator.xPullback_invert, xInversion]
    rw [xAddValuation, xAddValuation, monomialAddValuation_domCongr]
    apply congrArg (fun w => monomialAddValuation (k := k) w f)
    apply Finsupp.addHom_ext'
    intro i
    ext
    simp [Finsupp.linearCombination_single, ← Finsupp.single_neg]

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve.Cluster

variable {k ι Γ : Type*} [Field k] [DecidableEq ι]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {B C D : SkewExchangeMatrix ι}

local notation "trop" => Paths.lift (tropicalPrefunctor (A := Γ) ι)

/-- The pullback along a signed word transports the monomial valuation with
initial weights `b` to the valuation with the word's tropical weights. -/
theorem xAddValuation_xPullback (w : Word B C) (b : ι → Γ)
    (f : FractionRing (LaurentRing k ι)) :
    xAddValuation k b (w.xPullback k f) = xAddValuation k (Equiv.toFun ((trop).map w) b) f := by
  induction w generalizing f with
  | nil => simp [Paths.lift_nil, SingleObj.id_as_one]
  | cons w s ih =>
    obtain ⟨g, rfl⟩ := s
    rw [xPullback_cons, AlgEquiv.mul_apply, ih, Step.xPullback_eq,
      Generator.xAddValuation_xPullback]
    simp only [Equiv.toFun_as_coe, tropical_map_cons_apply, Step.tropical_apply]

/-- Over any field, equal X pullbacks give the same tropical action on tuples
in a linearly ordered abelian group. The words may have different endpoints. -/
theorem tropical_eq_of_xPullback_eq_of_linearOrder
    {w : Word B C} {v : Word B D} (h : w.xPullback k = v.xPullback k) :
    Equiv.toFun ((trop).map w) = Equiv.toFun ((trop).map v) := by
  funext b i
  apply WithTop.coe_injective
  rw [← xAddValuation_xCoordinate (k := k) _ i, ← xAddValuation_xCoordinate (k := k) _ i,
    ← w.xAddValuation_xPullback, ← v.xAddValuation_xPullback, h]

end Quiver.Path
