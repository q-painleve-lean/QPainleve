/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.HomogeneousLocalization
import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Polynomial coordinates on standard projective charts

Dehomogenizing at one variable identifies the degree-zero localization with a polynomial
ring on the remaining variables. The equivalence uses Tau Ceti's normalized coordinates
and its generation theorem `adjoin_range_awayXRatio`.
-/

public noncomputable section

open HomogeneousLocalization MvPolynomial

namespace TauCeti.MvPolynomial

attribute [local instance] _root_.MvPolynomial.gradedAlgebra

variable (R : Type*) [CommRing R] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

private theorem bijective_aeval_awayXRatio_succAbove (i : Fin (n + 1)) :
    Function.Bijective (aeval (R := R) (fun j ↦ awayXRatio (R := R) i (i.succAbove j))) := by
  let a : MvPolynomial (Fin n) R →ₐ[R] Away 𝒜 (X i) := aeval fun j ↦ awayXRatio i (i.succAbove j)
  have hi : dehomogenize (R := R) i (X i) = 1 := by simp
  let b := Away.lift 𝒜 (dehomogenize (R := R) i).toRingHom (hi ▸ isUnit_one)
  have hc := (dehomogenize (R := R) i).toRingHom.lift_comp_aeval_awayXRatio i hi
  have ha : a.comp (dehomogenize i) = aeval (awayXRatio (R := R) i) := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
    · simp [dehomogenize_X]
    · simp [a, dehomogenize_X]
  have hrename : a.toRingHom =
      (aeval (awayXRatio (R := R) i)).toRingHom.comp (rename i.succAbove).toRingHom := by
    have h : a = (aeval (awayXRatio (R := R) i)).comp (rename i.succAbove) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [a]
    exact congrArg AlgHom.toRingHom h
  constructor
  · have hid : b.comp a.toRingHom = RingHom.id _ := by
      rw [hrename, ← RingHom.comp_assoc, hc]
      apply RingHom.ext
      intro p
      exact dehomogenize_rename_succAbove i p
    exact Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hid x)
  · have hsurj : Function.Surjective (aeval (R := R) (awayXRatio (R := R) i)) := by
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
      exact adjoin_range_awayXRatio i
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨dehomogenize i p, (DFunLike.congr_fun ha p).trans hp⟩

/-- The chart at `X i` has one polynomial variable for each retained coordinate, in
the order given by `Fin.succAbove`. Each variable maps to the ratio `X (i.succAbove j) / X i`. -/
def mvPolynomialEquivAwayX (i : Fin (n + 1)) :
    MvPolynomial (Fin n) R ≃ₐ[R] Away 𝒜 (X i) :=
  AlgEquiv.ofBijective _ (bijective_aeval_awayXRatio_succAbove R i)

/-- The polynomial generator is the corresponding normalized homogeneous coordinate. -/
@[simp]
theorem mvPolynomialEquivAwayX_X (i : Fin (n + 1)) (j : Fin n) :
    mvPolynomialEquivAwayX R i (X j) = awayXRatio (R := R) i (i.succAbove j) :=
  aeval_X _ _

end TauCeti.MvPolynomial
