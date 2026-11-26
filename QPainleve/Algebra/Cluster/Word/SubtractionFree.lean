/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.Algebra.Cluster.Word.Seed
public import QPainleve.Algebra.Cluster.XMutation.SubtractionFree
import TauCeti.Algebra.MvPolynomial.Laurent.Basic

/-!
# Subtraction-free substitution along signed cluster words

In characteristic zero, the X pullback of a signed cluster word acts on any subtraction-free
rational expression by substitution of the final universal Y-seed's coefficients. This
includes relabeling and signed inversion as well as Tau Ceti's coefficient mutation.
-/

public noncomputable section

open Quiver QPainleve.Cluster TauCeti

variable (k : Type*) [Field k] [CharZero k] {ι : Type*} [DecidableEq ι]

local notation "XField" => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

namespace QPainleve.Cluster.Generator

/-- An elementary X pullback on subtraction-free expressions is substitution of the
universal Y-seed coefficients after the corresponding operation. -/
theorem xPullback_comp_toXField (g : Generator ι) (B : SkewExchangeMatrix ι) :
    (g.xPullback k B : XField →+* XField).comp (QsfZero.toXField k) =
      (QsfZero.toXField k).comp (QsfZero.eval (g.ySeed ⟨Qsf.X, B.val⟩).coefficient) := by
  cases g with
  | mutate p =>
    simpa [SkewExchangeMatrix.val_matrix_apply_swap] using xMutation_comp_toXField k B.val p
  | permute σ =>
    apply QsfZero.hom_ext
    intro i
    simp [Qsf.val_X]
  | invert =>
    apply QsfZero.hom_ext
    intro i
    simp [Qsf.val_X, Units.val_inv_eq_inv_val]

end QPainleve.Cluster.Generator

namespace Quiver.Path

variable {B C : SkewExchangeMatrix ι}

/-- The X pullback of a signed word on subtraction-free expressions is evaluation at the
coefficients obtained by applying the word to the universal Y-seed. -/
theorem xPullback_comp_toXField_eq_eval_ySeed (w : Word B C) :
    (w.xPullback k : XField →+* XField).comp (QsfZero.toXField k) =
      (QsfZero.toXField k).comp (QsfZero.eval (w.ySeed ⟨Qsf.X, B.val⟩).coefficient) := by
  induction w with
  | nil => ext i; simp
  | @cons C D w e ih =>
    let s : YSeed ι (Qsf ι) := w.ySeed ⟨Qsf.X, B.val⟩
    let t : YSeed ι (Qsf ι) := ⟨Qsf.X, C.val⟩
    let g := Step.generator e
    have hs : t.map (Qsf.eval s.coefficient) = s := by
      apply YSeed.ext
      · funext i
        simp [t]
      · rw [YSeed.map_exchangeMatrix]
        exact (w.ySeed_exchangeMatrix ⟨Qsf.X, B.val⟩ rfl).symm
    have hEval : (QsfZero.eval s.coefficient).comp (QsfZero.eval (g.ySeed t).coefficient) =
        QsfZero.eval (g.ySeed s).coefficient := by
      apply QsfZero.hom_ext
      intro i
      simp only [RingHom.comp_apply, QsfZero.eval_X]
      rw [← Qsf.val_eval, ← YSeed.map_coefficient, Generator.map_ySeed, hs]
    simp only [ySeed_cons, xPullback_cons, Step.xPullback_eq, AlgEquiv.aut_mul,
      AlgEquiv.toRingHom_trans]
    rw [RingHom.comp_assoc, g.xPullback_comp_toXField k C, ← RingHom.comp_assoc, ih,
      RingHom.comp_assoc, hEval]

/-- Pullback on the image of the universal coefficient semifield is substitution at
the final Y-seed coefficients. -/
theorem xPullback_toXField_eval_ySeed (k : Type*) [Field k] [CharZero k]
    {B C : SkewExchangeMatrix ι} (w : Word B C) (x : Qsf ι) :
    w.xPullback k (QsfZero.toXField k (x : QsfZero ι)) =
      QsfZero.toXField k
        (Qsf.eval (w.ySeed ⟨Qsf.X, B.val⟩).coefficient x : QsfZero ι) := by
  rw [Qsf.val_eval]
  exact DFunLike.congr_fun (w.xPullback_comp_toXField_eq_eval_ySeed k) (x : QsfZero ι)

/-- Each X coordinate is pulled back to the corresponding coefficient of the final
universal Y-seed, interpreted in the field of independent X coordinates. -/
theorem xPullback_xCoordinate_eq_toXField (w : Word B C) (i : ι) :
    w.xPullback k (xCoordinate k i) =
      QsfZero.toXField k ((w.ySeed ⟨Qsf.X, B.val⟩).coefficient i : QsfZero ι) := by
  simpa using DFunLike.congr_fun (w.xPullback_comp_toXField_eq_eval_ySeed k) (QsfZero.X i)

/-- Two signed words with a common source have the same X pullback exactly when their final
universal coefficient families agree. Their endpoint matrices may differ. -/
theorem xPullback_eq_iff_ySeed_coefficient_eq {D : SkewExchangeMatrix ι}
    (w : Word B C) (v : Word B D) :
    w.xPullback k = v.xPullback k ↔
      (w.ySeed ⟨Qsf.X, B.val⟩).coefficient = (v.ySeed ⟨Qsf.X, B.val⟩).coefficient := by
  constructor
  · intro h
    funext i
    apply Units.ext
    apply QsfZero.toXField_injective k
    rw [← w.xPullback_xCoordinate_eq_toXField k i, ← v.xPullback_xCoordinate_eq_toXField k i, h]
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply IsLocalization.algHom_ext (nonZeroDivisors (LaurentRing k ι))
    apply LaurentRing.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.toAlgHom_apply,
      Algebra.algHom, LaurentRing.X_def, ← xCoordinate_def] using
      (w.xPullback_xCoordinate_eq_toXField k i).trans
        ((congrArg (fun c : ι → Qsf ι ↦ QsfZero.toXField k (c i : QsfZero ι)) h).trans
          (v.xPullback_xCoordinate_eq_toXField k i).symm)

end Quiver.Path
