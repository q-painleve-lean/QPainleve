/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Word
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Universal
public import TauCeti.Algebra.Cluster.YSeed.Word
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import QPainleve.Geometry.Toric.CharacterTorus.Basic
import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

/-!
# Subtraction-free comparison for cluster X mutation

In characteristic zero, the universal subtraction-free semifield embeds in the field of
independent X coordinates. Its variables become the unit-exponent Laurent monomials. Mutation
in that field intertwines the universal coefficient substitution, so a finite mutation word
acts on the independent X coordinates by the coefficients of Tau Ceti's `YSeed.mutationWord`.

The comparison uses Tau Ceti's `QsfZero.toFractionRing`, `MvPolynomial.toLaurent` and
`YSeed.mutation_coefficient_of_ne`. The X convention is that of Fock and Goncharov,
*Cluster ensembles, quantization and the dilogarithm*, §1.2.2 (7) and §1.2.4 (13).
-/

public noncomputable section

open TauCeti

variable (k : Type*) [Field k] {ι : Type*}

local notation "XField" => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

namespace TauCeti.QsfZero

variable [CharZero k]

private def intPolynomialToXField : MvPolynomial ι ℤ →+* XField :=
  (algebraMap (LaurentRing k ι) XField).comp
    ((MvPolynomial.toLaurent : MvPolynomial ι k →ₐ[k] LaurentRing k ι).toRingHom.comp
      (MvPolynomial.map (Int.castRingHom k)))

private theorem intPolynomialToXField_injective :
    Function.Injective (intPolynomialToXField k (ι := ι)) :=
  (IsFractionRing.injective (LaurentRing k ι) XField).comp
    (MvPolynomial.toLaurent_injective.comp (MvPolynomial.map_injective _ Int.cast_injective))

/-- Interpret subtraction-free rational functions with zero in the field of independent cluster
X coordinates, using the unique coefficient map from the integers. -/
def toXField : QsfZero ι →+* XField :=
  (IsFractionRing.lift (K := FractionRing (MvPolynomial ι ℤ))
    (intPolynomialToXField_injective k)).comp (toFractionRing ι)

/-- The characteristic-zero interpretation is faithful. -/
theorem toXField_injective : Function.Injective (toXField k (ι := ι)) := by
  unfold toXField
  exact (RingHom.injective (IsFractionRing.lift (K := FractionRing (MvPolynomial ι ℤ))
    (intPolynomialToXField_injective k))).comp toFractionRing_injective

/-- A universal variable maps to the corresponding independent X coordinate. -/
@[simp]
theorem toXField_X (i : ι) : toXField k (X i) = QPainleve.Cluster.xCoordinate k i := by
  simp [toXField, intPolynomialToXField, IsFractionRing.lift_algebraMap,
    QPainleve.Cluster.xCoordinate_def, LaurentRing.X_def]

end TauCeti.QsfZero

namespace QPainleve.Cluster

variable [DecidableEq ι] [CharZero k]

/-- A native mutation with independent initial coefficients gives the pullback of each
independent X coordinate. -/
theorem toXField_mutation_coefficient (B : ExchangeMatrix (Function.Embedding.refl ι))
    (p i : ι) :
    QsfZero.toXField k (((⟨Qsf.X, B⟩ : YSeed ι (Qsf ι)).mutation p).coefficient i : QsfZero ι) =
      xMutation k p (fun i ↦ B.matrix p i) (xCoordinate k i) := by
  by_cases hi : i = p
  · subst i
    simp [Qsf.val_X]
  · rw [YSeed.mutation_coefficient_of_ne _ hi, xMutation_apply_of_ne _ _ _ hi]
    simp [Qsf.val_X, posPart_def, add_comm]

/-- Applying the field pullback to any subtraction-free expression is the same as evaluating
the expression at the mutated universal coefficients. -/
theorem xMutation_comp_toXField (B : ExchangeMatrix (Function.Embedding.refl ι)) (p : ι) :
    (xMutation k p (fun i ↦ B.matrix p i) : XField →+* XField).comp (QsfZero.toXField k) =
      (QsfZero.toXField k).comp
        (QsfZero.eval (((⟨Qsf.X, B⟩ : YSeed ι (Qsf ι)).mutation p).coefficient)) := by
  apply QsfZero.hom_ext
  intro i
  simpa only [RingHom.comp_apply, QsfZero.toXField_X, QsfZero.eval_X,
    ← AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom]
    using (toXField_mutation_coefficient k B p i).symm

/-- Substitution into an arbitrary subtraction-free expression along a native mutation word
agrees with applying the composite X pullback to that expression. -/
theorem xMutationWord_comp_toXField (B : ExchangeMatrix (Function.Embedding.refl ι))
    (w : List ι) :
    (xMutationWord k B w : XField →+* XField).comp (QsfZero.toXField k) =
      (QsfZero.toXField k).comp
        (QsfZero.eval (((⟨Qsf.X, B⟩ : YSeed ι (Qsf ι)).mutationWord w).coefficient)) := by
  induction w generalizing B with
  | nil => simp
  | cons p w ih =>
    simp only [xMutationWord_cons, AlgEquiv.toRingHom_trans, RingHom.comp_assoc, ih]
    rw [← RingHom.comp_assoc, xMutation_comp_toXField, RingHom.comp_assoc]
    congr 1
    let s : YSeed ι (Qsf ι) := ⟨Qsf.X, B⟩
    have h : (⟨Qsf.X, B.mutation p⟩ : YSeed ι (Qsf ι)).map
        (Qsf.eval (s.mutation p).coefficient) = s.mutation p := by
      ext i <;> simp [s]
    apply QsfZero.hom_ext
    intro i
    simp only [RingHom.comp_apply, QsfZero.eval_X, YSeed.mutationWord_cons]
    rw [← Qsf.val_eval, ← YSeed.map_coefficient, YSeed.map_mutationWord, h]

/-- The coefficients of a native mutation word, started at the independent variables, are
exactly the Laurent field pullbacks of those variables. -/
theorem toXField_mutationWord_coefficient (B : ExchangeMatrix (Function.Embedding.refl ι))
    (w : List ι) (i : ι) :
    QsfZero.toXField k (((⟨Qsf.X, B⟩ : YSeed ι (Qsf ι)).mutationWord w).coefficient i :
      QsfZero ι) = xMutationWord k B w (xCoordinate k i) := by
  simpa only [RingHom.comp_apply, QsfZero.toXField_X, QsfZero.eval_X,
    ← AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom]
    using (DFunLike.congr_fun (xMutationWord_comp_toXField k B w) (QsfZero.X i)).symm

/-- Substitution of the final coefficients of a native mutation word extends uniquely to an
automorphism of the field of independent X coordinates. -/
theorem existsUnique_xPullback_mutationWord (B : ExchangeMatrix (Function.Embedding.refl ι))
    (w : List ι) :
    ∃! f : XField ≃ₐ[k] XField, ∀ a : QsfZero ι,
      f (QsfZero.toXField k a) = QsfZero.toXField k
        (QsfZero.eval ((⟨Qsf.X, B⟩ : YSeed ι (Qsf ι)).mutationWord w).coefficient a) := by
  have hword (a : QsfZero ι) :=
    DFunLike.congr_fun (xMutationWord_comp_toXField k B w) a
  simp only [RingHom.comp_apply, ← AlgEquiv.toAlgHom_toRingHom, AlgHom.coe_toRingHom,
    AlgEquiv.coe_toAlgHom] at hword
  refine ⟨xMutationWord k B w, hword, fun f hf ↦ ?_⟩
  apply AlgEquiv.coe_toAlgHom_injective
  apply CharacterTorus.functionField_hom_ext_basis Finsupp.basisSingleOne
  intro i
  simpa only [Finsupp.coe_basisSingleOne, CharacterTorus.monomial_ofAdd, ← xCoordinate_def,
    AlgEquiv.coe_toAlgHom, QsfZero.toXField_X] using
      (hf (QsfZero.X i)).trans (hword (QsfZero.X i)).symm

end QPainleve.Cluster
