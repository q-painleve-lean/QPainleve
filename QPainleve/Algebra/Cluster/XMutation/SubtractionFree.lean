/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.XMutation.Basic
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Universal
public import TauCeti.Algebra.Cluster.YSeed.Word
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import QPainleve.Geometry.Toric.CharacterTorus.Basic
import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

/-!
# Subtraction-free X mutation

In characteristic zero the subtraction-free rational functions, including zero, embed in the
field of independent X coordinates. Under this embedding, substitution of the coefficients of
a mutated universal Y-seed is the X pullback on every subtraction-free rational function.
For any native mutation word, the final seed determines a unique field pullback extending
this substitution.

The comparison uses Tau Ceti's `QsfZero.toFractionRing`, `MvPolynomial.toLaurent`, and
`YSeed.mutation_coefficient_of_ne`. Native Y-seed mutation uses the mutation row, which is the
geometric mutation column under the convention `B = -ε` for a skew-symmetric exchange matrix.
-/

public noncomputable section

namespace QPainleve.Cluster

open TauCeti
open scoped Int

variable (k : Type*) [Field k] [CharZero k] {ι : Type*}

local notation "Functions" => FractionRing (LaurentRing k ι)

/-- Interpret a subtraction-free rational function in the field of independent X coordinates.
The integer-coefficient rational functions enter by coefficient extension and the inclusion of
polynomials in Laurent polynomials. -/
def qsfToXFunctionField : QsfZero ι →+* Functions := by
  let polynomialMap : MvPolynomial ι ℤ →+* Functions :=
    (algebraMap (LaurentRing k ι) Functions).comp
      (MvPolynomial.toLaurent.toRingHom.comp (MvPolynomial.map (Int.castRingHom k)))
  have h : Function.Injective polynomialMap := by
    simpa only [polynomialMap, RingHom.coe_comp, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using
      (IsFractionRing.injective (LaurentRing k ι) Functions).comp
        (MvPolynomial.toLaurent_injective.comp
          (MvPolynomial.map_injective (Int.castRingHom k) Int.cast_injective))
  exact (IsFractionRing.lift h).comp (QsfZero.toFractionRing ι)

/-- Equality of subtraction-free rational functions is detected in the X function field. -/
theorem qsfToXFunctionField_injective :
    Function.Injective (qsfToXFunctionField k : QsfZero ι → Functions) := by
  rw [qsfToXFunctionField, RingHom.coe_comp]
  exact (RingHom.injective _).comp QsfZero.toFractionRing_injective

/-- The subtraction-free variable maps to the corresponding independent coordinate. -/
@[simp] theorem qsfToXFunctionField_X (i : ι) :
    qsfToXFunctionField k (QsfZero.X i) = xCoordinate k i := by
  simp [qsfToXFunctionField, IsFractionRing.lift_algebraMap, LaurentRing.X_def, xCoordinate_def]

variable [DecidableEq ι]

/-- On subtraction-free rational functions, X mutation is substitution of the mutated
universal Y-seed coefficients. The row of the native exchange matrix supplies the exponents. -/
theorem xMutation_comp_qsfToXFunctionField
    (B : ExchangeMatrix (Function.Embedding.refl ι)) (p : ι) :
    ((xMutation k p (fun i ↦ B.matrix p i)).toAlgHom : Functions →+* Functions).comp
        (qsfToXFunctionField k) =
      (qsfToXFunctionField k).comp
        (QsfZero.eval ((YSeed.mk Qsf.X B : YSeed ι (Qsf ι)).mutation p).coefficient) := by
  apply QsfZero.hom_ext
  intro i
  simp only [RingHom.comp_apply, qsfToXFunctionField_X, AlgHom.coe_toRingHom,
    AlgEquiv.coe_toAlgHom, QsfZero.eval_X]
  by_cases hi : i = p
  · subst i
    simp [Units.val_inv_eq_inv_val]
  · rw [xMutation_apply_of_ne _ _ _ hi, YSeed.mutation_coefficient_of_ne _ hi]
    simp [posPart_def, Units.val_zpow_eq_zpow_val, add_comm]

/-- Substitution of the final coefficients of a native mutation word extends uniquely to a
pullback on the field of independent X coordinates. -/
theorem existsUnique_xPullback_mutationWord
    (B : ExchangeMatrix (Function.Embedding.refl ι)) (w : List ι) :
    ∃! f : Functions ≃ₐ[k] Functions, ∀ a : QsfZero ι,
      f (qsfToXFunctionField k a) = qsfToXFunctionField k
        (QsfZero.eval ((YSeed.mk Qsf.X B : YSeed ι (Qsf ι)).mutationWord w).coefficient a) := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- Construct the pullback by composing the first mutation with the remaining word.
    induction w generalizing B with
    | nil => exact ⟨AlgEquiv.refl, fun a ↦ by simp⟩
    | cons p w ih =>
      let mutated : YSeed ι (Qsf ι) := (YSeed.mk Qsf.X B).mutation p
      let fresh : YSeed ι (Qsf ι) := YSeed.mk Qsf.X (B.mutation p)
      let substitution := QsfZero.eval mutated.coefficient
      have hmap : fresh.map substitution.mapUnits = mutated := by
        apply YSeed.ext
        · funext i
          simp [fresh, substitution, Qsf.mapUnits_eval]
        · simp [fresh, mutated]
      obtain ⟨f, hf⟩ := ih (B.mutation p)
      refine ⟨f.trans (xMutation k p (fun i ↦ B.matrix p i)), fun a ↦ ?_⟩
      have hp := DFunLike.congr_fun (xMutation_comp_qsfToXFunctionField k B p)
        (QsfZero.eval (fresh.mutationWord w).coefficient a)
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom] at hp
      rw [AlgEquiv.trans_apply, hf, hp, QsfZero.map_eval substitution, YSeed.mutationWord_cons]
      have hword := (fresh.map_mutationWord substitution.mapUnits w).trans
        (congrArg (fun seed ↦ seed.mutationWord w) hmap)
      rw [← hword]
      apply congrArg (fun coefficients ↦ qsfToXFunctionField k (QsfZero.eval coefficients a))
      funext i
      apply Units.ext
      simp only [YSeed.map_coefficient, RingHom.val_mapUnits, Units.coe_map]
      rfl
  · intro f g hf hg
    apply AlgEquiv.coe_toAlgHom_injective
    apply CharacterTorus.functionField_hom_ext_basis Finsupp.basisSingleOne
    intro i
    have hi := (hf (QsfZero.X i)).trans (hg (QsfZero.X i)).symm
    simpa only [Finsupp.coe_basisSingleOne, CharacterTorus.monomial_ofAdd, ← xCoordinate_def,
      AlgEquiv.coe_toAlgHom, qsfToXFunctionField_X] using hi

end QPainleve.Cluster
