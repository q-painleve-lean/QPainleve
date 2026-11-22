/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# Standard smoothness of Laurent coordinate algebras

Adjoining finitely many invertible variables gives a standard smooth algebra of relative
dimension the number of variables. The proof uses Mathlib's
`AddMonoidAlgebra.curryAlgEquiv` to add one variable at a time and Tau Ceti's
`LaurentPolynomial.isLocalization` for the one-variable localization.
-/

public section

open Algebra

namespace AddMonoidAlgebra

variable (R : Type*) [CommRing R]

private theorem isStandardSmoothOfRelativeDimension_finsupp_fin_int (n : ℕ) :
    IsStandardSmoothOfRelativeDimension n R (AddMonoidAlgebra R (Fin n →₀ ℤ)) := by
  induction n with
  | zero =>
    exact IsStandardSmoothOfRelativeDimension.of_algEquiv 0
      (AddMonoidAlgebra.uniqueAlgEquiv R (A := R) (Fin 0 →₀ ℤ)).symm
  | succ n ih =>
    let S := AddMonoidAlgebra R (Fin n →₀ ℤ)
    let P := LaurentPolynomial S
    let e : (Fin (n + 1) →₀ ℤ) ≃+ ℤ × (Fin n →₀ ℤ) :=
      (Finsupp.domCongr finSumFinEquiv.symm).trans <|
        Finsupp.sumFinsuppAddEquivProdFinsupp.trans <|
          ((AddEquiv.refl _).prodCongr (Finsupp.uniqueAddEquiv (0 : Fin 1))).trans
            AddEquiv.prodComm
    have : IsStandardSmoothOfRelativeDimension 1 S (Polynomial S) :=
      IsStandardSmoothOfRelativeDimension.of_algEquiv 1
        (MvPolynomial.uniqueAlgEquiv S (Fin 1))
    have : IsStandardSmoothOfRelativeDimension 0 (Polynomial S) P :=
      IsStandardSmoothOfRelativeDimension.localization_away (Polynomial.X : Polynomial S)
    have : IsStandardSmoothOfRelativeDimension 1 S P := by
      simpa using IsStandardSmoothOfRelativeDimension.trans S (Polynomial S) P
        (n := 1) (m := 0)
    have : IsStandardSmoothOfRelativeDimension (n + 1) R P := by
      simpa only [Nat.add_comm] using
        IsStandardSmoothOfRelativeDimension.trans R S P (n := n) (m := 1)
    exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n + 1)
      (((domCongr R R e).trans (curryAlgEquiv R)).symm)

/-- The Laurent coordinate algebra in finitely many variables is standard smooth of relative
dimension the number of variables. -/
theorem isStandardSmoothOfRelativeDimension_finsupp_int (ι : Type*) [Finite ι] :
    IsStandardSmoothOfRelativeDimension (Nat.card ι) R (AddMonoidAlgebra R (ι →₀ ℤ)) := by
  let := Fintype.ofFinite ι
  have := isStandardSmoothOfRelativeDimension_finsupp_fin_int R (Nat.card ι)
  let e := Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := ι)).symm
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (Nat.card ι)
    (domCongr R R (Finsupp.domCongr e.symm))

end AddMonoidAlgebra
