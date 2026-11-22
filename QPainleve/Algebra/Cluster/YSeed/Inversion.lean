/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Algebra.Cluster.YSeed.Basic

/-!
# Inversion of Y-seeds

Simultaneous inversion of the coefficients and negation of the exchange matrix commute
with mutation, relabeling, and specialization of the coefficient semifield. The signed
seed operation follows Bershtein, Gavrylenko, and Marshakov,
*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1.
-/

public section

namespace TauCeti.YSeed

variable {ι κ P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Invert every coefficient and negate the exchange matrix, retaining its symmetrizer. -/
def invert (s : YSeed ι P) : YSeed ι P where
  coefficient i := (s.coefficient i)⁻¹
  exchangeMatrix :=
    { s.exchangeMatrix with
      matrix := -s.exchangeMatrix.matrix
      isSkewSymmetrizer := s.exchangeMatrix.isSkewSymmetrizer.neg }

@[simp]
theorem invert_coefficient (s : YSeed ι P) (i : ι) :
    s.invert.coefficient i = (s.coefficient i)⁻¹ :=
  (rfl)

@[simp]
theorem invert_exchangeMatrix_matrix (s : YSeed ι P) :
    s.invert.exchangeMatrix.matrix = -s.exchangeMatrix.matrix :=
  (rfl)

@[simp]
theorem invert_exchangeMatrix_symmetrizer (s : YSeed ι P) :
    s.invert.exchangeMatrix.symmetrizer = s.exchangeMatrix.symmetrizer :=
  (rfl)

/-- Signed inversion is an involution. -/
@[simp]
theorem invert_invert (s : YSeed ι P) : s.invert.invert = s := by
  apply YSeed.ext
  · funext i
    simp
  · apply ExchangeMatrix.ext <;> simp

/-- Signed inversion commutes with specializing coefficients. -/
@[simp]
theorem map_invert (s : YSeed ι P) (f : CoefficientSemifieldHom P Q) :
    s.invert.map f = (s.map f).invert := by
  apply YSeed.ext
  · funext i
    simp
  · apply ExchangeMatrix.ext <;> simp

/-- Signed inversion commutes with relabeling. -/
@[simp]
theorem reindex_invert (s : YSeed ι P) (e : ι ≃ κ) :
    reindex e s.invert = (reindex e s).invert := by
  apply YSeed.ext
  · funext i
    simp
  · apply ExchangeMatrix.ext
    · ext i j
      simp
    · simp

/-- Mutating the inverted Y-seed gives the inversion of the mutated Y-seed. -/
@[simp]
theorem mutation_invert [DecidableEq ι] (s : YSeed ι P) (p : ι) :
    s.invert.mutation p = (s.mutation p).invert := by
  apply YSeed.ext
  · funext i
    by_cases h : i = p
    · subst i
      simp
    · simp only [mutation_coefficient_of_ne _ h, invert_coefficient,
        invert_exchangeMatrix_matrix, Matrix.neg_apply, neg_neg]
      have hCorrection (a : P) (b : ℤ) :
          a⁻¹ ^ (-b)⁺ * (a⁻¹ + 1) ^ b = a⁻¹ ^ b⁺ * (a + 1) ^ b := by
        have hBinomial : a⁻¹ + 1 = (a + 1) / a := by
          simpa using CoefficientSemifield.inv_add_inv a (1 : P)
        have hExponent : (-b)⁺ + b = b⁺ := by
          rw [posPart_neg]
          have := posPart_sub_negPart b
          omega
        rw [hBinomial, div_zpow, div_eq_mul_inv, ← inv_zpow a b]
        rw [mul_comm ((a + 1) ^ b), ← mul_assoc, ← zpow_add, hExponent]
      rw [mul_assoc, hCorrection]
      simp only [mul_inv_rev, zpow_neg, inv_inv, inv_zpow]
      ac_rfl
  · apply ExchangeMatrix.ext
    · simp
    · simp

end TauCeti.YSeed
