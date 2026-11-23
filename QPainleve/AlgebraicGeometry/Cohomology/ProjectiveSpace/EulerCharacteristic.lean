/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Euler characteristics of twists on projective space

On projective space of positive dimension `d`, the Euler characteristic of `𝒪(m)` is the
integer binomial coefficient `Ring.choose (m + d) d`, for every integer twist `m`. On the
projective plane this gives the quadratic formula used as the starting point for computing
Euler characteristics on blowups of the plane. The structure sheaf of the projective plane
also has vanishing cohomology in positive degrees.

The calculation uses Tau Ceti's Čech computation of the top cohomology, following the Stacks
Project, Lemma 30.8.1 (tag 01XT). Subtracting each negative exponent from `-1` identifies its
monomial basis with ordinary monomials in the complementary degree.
-/

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped BigOperators

universe u

namespace QPainleve

open TauCeti.SymmetricAlgebra

public section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Complementing each exponent with respect to `-1` identifies Laurent monomials whose
exponents are all negative with ordinary monomials in the complementary degree. -/
noncomputable def negativeExponentsEquivSym (j : ℕ) :
    negativeExponents ι (-(j : ℤ) - Fintype.card ι) ≃ Sym ι j := by
  let complement : negativeExponents ι (-(j : ℤ) - Fintype.card ι) ≃
      {s : ι → ℕ // ∑ i, s i = j} :=
    { toFun := fun e ↦ ⟨fun i ↦ (-1 - e.val i).toNat, by
        have he := mem_negativeExponents.mp e.property
        have hcast (i : ι) : ((-1 - e.val i).toNat : ℤ) = -1 - e.val i :=
          Int.toNat_of_nonneg (by have := he.2 i; omega)
        have h : ((∑ i, (-1 - e.val i).toNat : ℕ) : ℤ) = j := by
          simp [Nat.cast_sum, hcast, Finset.sum_sub_distrib, he.1]
          ring
        exact_mod_cast h⟩
      invFun := fun s ↦ ⟨fun i ↦ -1 - (s.val i : ℤ), mem_negativeExponents.mpr ⟨by
        have hs : (∑ i, (s.val i : ℤ)) = j := by exact_mod_cast s.property
        simp [Finset.sum_sub_distrib, hs]
        ring, fun i ↦ by omega⟩⟩
      left_inv := fun e ↦ Subtype.ext <| funext fun i ↦ by
        have hi := (mem_negativeExponents.mp e.property).2 i
        dsimp
        omega
      right_inv := fun s ↦ Subtype.ext <| funext fun i ↦ by
        dsimp
        omega }
  exact complement.trans (Sym.equivNatSumOfFintype ι j).symm

/-- The multiplicity of a variable in the complementary monomial is `-1 - eᵢ`. -/
@[simp]
theorem negativeExponentsEquivSym_apply (j : ℕ)
    (e : negativeExponents ι (-(j : ℤ) - Fintype.card ι)) (i : ι) :
    Multiset.count i (negativeExponentsEquivSym ι j e) = (-1 - e.val i).toNat := by
  rw [← Sym.coe_equivNatSumOfFintype_apply_apply]
  simp [negativeExponentsEquivSym]

/-- A variable of multiplicity `a` has exponent `-1 - a` in the inverse Laurent monomial. -/
@[simp]
theorem negativeExponentsEquivSym_symm_apply (j : ℕ) (s : Sym ι j) (i : ι) :
    ((negativeExponentsEquivSym ι j).symm s).val i = -1 - (Multiset.count i s : ℤ) := by
  simp [negativeExponentsEquivSym]

end

end QPainleve

namespace Module.Basis

open QPainleve TauCeti.SymmetricAlgebra Scheme.Modules

/-- On projective space of dimension `n + 1`, the top cohomology of `𝒪(-j-n-2)` has
rank equal to the number of degree-`j` monomials in the homogeneous coordinates. -/
public theorem finrank_cohomology_top_twistingSheaf_eq_multichoose
    {R M : Type u} [CommRing R] [Nontrivial R] [AddCommMonoid M] [Module R M]
    {ι : Type*} [Fintype ι] (b : Basis ι R M) (j : ℕ) {n : ℕ} (hn : Fintype.card ι = n + 2) :
    Module.finrank R (Cohomology
      (Proj.twistingSheaf (homogeneousSubmodule R M) (-(j : ℤ) - Fintype.card ι)) (n + 1)) =
      (Fintype.card ι).multichoose j := by
  classical
  rw [b.finrank_cohomology_top_twistingSheaf _ hn, Nat.card_congr (negativeExponentsEquivSym ι j),
    Sym.natCard_sym_eq_multichoose, Nat.card_eq_fintype_card]

section

variable {k M : Type u} [Field k] [AddCommMonoid M] [Module k M]
  {ι : Type*} [Fintype ι]

local notation "𝒜" => homogeneousSubmodule k M

private theorem eulerCharBelow_twistingSheaf_eq_endpoints
    (b : Basis ι k M) (m : ℤ) {n : ℕ} (hn : Fintype.card ι = n + 2) :
    eulerCharBelow k (Proj 𝒜) (Proj.twistingSheaf 𝒜 m) (n + 2) =
      (Module.finrank k (Cohomology (Proj.twistingSheaf 𝒜 m) 0) : ℤ) +
        (-1) ^ (n + 1) * (Module.finrank k (Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1)) : ℤ) := by
  have hbelow (q : ℕ) (hq : q ≤ n) :
      eulerCharBelow k (Proj 𝒜) (Proj.twistingSheaf 𝒜 m) (q + 1) =
        (Module.finrank k (Cohomology (Proj.twistingSheaf 𝒜 m) 0) : ℤ) := by
    induction q with
    | zero => simp
    | succ q ih =>
      have := b.subsingleton_cohomology_twistingSheaf_of_lt_card m (Nat.succ_pos q)
        (by rw [hn]; omega)
      rw [eulerCharBelow_succ, ih (by omega)]
      simp [Module.finrank_zero_of_subsingleton]
  rw [eulerCharBelow_succ, hbelow n le_rfl]

/-- The Euler characteristic of `𝒪(m)` on projective space of positive dimension `n + 1` is
the integer binomial coefficient `(m + n + 1).choose (n + 1)`. All higher degrees vanish
and all cohomology is finite-dimensional by the twisting-sheaf cohomology calculation. -/
public theorem eulerCharBelow_twistingSheaf (b : Basis ι k M) (m : ℤ) {n : ℕ}
    (hn : Fintype.card ι = n + 2) :
    eulerCharBelow k (Proj 𝒜) (Proj.twistingSheaf 𝒜 m) (n + 2) =
      Ring.choose (m + ((n + 1 : ℕ) : ℤ)) (n + 1) := by
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hn]; omega)
  have hcount (j : ℕ) : (n + 2).multichoose j = (j + (n + 1)).choose (n + 1) := by
    have h : n + 2 + j - 1 = j + (n + 1) := by omega
    rw [Nat.multichoose_eq, h, Nat.choose_symm_add]
  rw [eulerCharBelow_twistingSheaf_eq_endpoints b m hn]
  rcases le_or_gt 0 m with hm | hm
  · have := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (m := m) (q := n + 1)
      (by rw [hn]; omega) (Nat.succ_pos n)
    lift m to ℕ using hm
    rw [Module.finrank_zero_of_subsingleton (M := Cohomology (Proj.twistingSheaf 𝒜 m) (n + 1)),
      Nat.cast_zero, mul_zero, add_zero, finrank_cohomology_zero_twistingSheaf m b, hn, hcount,
      ← Nat.cast_add, Ring.choose_natCast]
  have := subsingleton_cohomology_zero_twistingSheaf_of_neg hm b
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, zero_add]
  by_cases hnear : -((n + 1 : ℕ) : ℤ) ≤ m
  · have := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (m := m) (q := n + 1)
      (by rw [hn]; omega) (Nat.succ_pos n)
    have hnonneg : 0 ≤ m + ((n + 1 : ℕ) : ℤ) := by omega
    let j := (m + ((n + 1 : ℕ) : ℤ)).toNat
    have hjcast : (j : ℤ) = m + ((n + 1 : ℕ) : ℤ) := Int.toNat_of_nonneg hnonneg
    have hjlt : j < n + 1 := by omega
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero, ← hjcast,
      Ring.choose_natCast, Nat.choose_eq_zero_of_lt hjlt, Nat.cast_zero]
  · let j := (-m - ((n + 2 : ℕ) : ℤ)).toNat
    have hj : (j : ℤ) = -m - ((n + 2 : ℕ) : ℤ) := Int.toNat_of_nonneg (by omega)
    have htop : m = -(j : ℤ) - Fintype.card ι := by rw [hn]; omega
    have hbinom : m + ((n + 1 : ℕ) : ℤ) = -((j : ℤ) + 1) := by omega
    rw [hbinom, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul]
    have hadd : (j : ℤ) + 1 + ((n + 1 : ℕ) : ℤ) - 1 = ((j + (n + 1) : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hadd, Ring.choose_natCast, htop, b.finrank_cohomology_top_twistingSheaf_eq_multichoose
      j hn, hn, hcount, Int.cast_id]

end

end Module.Basis

namespace QPainleve

open Scheme.Modules TauCeti.SymmetricAlgebra

public section

/-- The Euler characteristic of `𝒪(m)` on the projective plane is `(m + 1)(m + 2)/2`,
including negative twists. -/
theorem eulerCharBelow_twistingSheaf_projectivePlane (k : Type u) [Field k] (m : ℤ) :
    eulerCharBelow k (Proj (homogeneousSubmodule k (Fin 3 → k)))
        (Proj.twistingSheaf (homogeneousSubmodule k (Fin 3 → k)) m) 3 =
      (m + 1) * (m + 2) / 2 := by
  rw [(Pi.basisFun k (Fin 3)).eulerCharBelow_twistingSheaf m (n := 1) (Fintype.card_fin 3)]
  have h := Ring.descPochhammer_eq_factorial_smul_choose (m + 2) 2
  rw [← Polynomial.eval_eq_smeval] at h
  norm_num [descPochhammer_succ_right] at h
  have hmul : (m + 1) * (m + 2) = 2 * Ring.choose (m + 2) 2 := by
    convert h using 1
    ring
  rw [hmul]
  norm_num

end

end QPainleve

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.CategoryTheory
open TauCeti.SymmetricAlgebra

variable (k : Type u) [CommRing k]

local notation "𝒮" => homogeneousSubmodule k (Fin 3 → k)
local notation "P" => Proj 𝒮

/-- The projective plane has vanishing structure-sheaf cohomology in positive degrees. -/
public theorem subsingleton_cohomology_trivial_projectivePlane {i : ℕ} (hi : 0 < i) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial P).obj i) := by
  have : Subsingleton (Cohomology (Proj.twistingSheaf 𝒮 0) i) :=
    (Pi.basisFun k (Fin 3)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt (by decide) hi
  let e := InvertibleSheaf.trivialObjIsoUnit P ≪≫ Proj.unitIsoTwistingSheafZero 𝒮
  exact (cohomologyBaseLinearEquivOfIso k e i).injective.subsingleton

end TauCeti.AlgebraicGeometry
