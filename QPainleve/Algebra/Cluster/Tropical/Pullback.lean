/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import QPainleve.Algebra.Cluster.Word.SubtractionFree

/-!
# Tropical evaluation of X pullbacks

Equality on the field of independent X coordinates in characteristic zero implies equality
under tropical evaluation. This uses the universal subtraction-free coefficient semifield and
applies to signed words with a common source, even when their terminal seeds differ.
-/

public section

open CategoryTheory QPainleve.Cluster TauCeti

namespace Quiver.Path

variable {ι : Type*} [DecidableEq ι] {A : Type*}
  [AddCommGroup A] [SemilatticeInf A] [IsOrderedAddMonoid A]
  {B C D : SkewExchangeMatrix ι}

local notation "trop" => Paths.lift (tropicalPrefunctor (A := A) ι)

/-- The tropical exponent action agrees with Y-seed evaluation over the infimum
tropical semifield. -/
@[simp]
theorem ySeed_tropicalSeed (w : Word B C) (b : ι → A) :
    w.ySeed (B.tropicalSeed b) = C.tropicalSeed (Equiv.toFun ((trop).map w) b) := by
  induction w with
  | nil => simp [Paths.lift_nil, SingleObj.id_as_one]
  | @cons C D w s ih =>
    obtain ⟨g, rfl⟩ := s
    simp only [ySeed_cons, ih, Equiv.toFun_as_coe, tropical_map_cons_apply, Step.tropical_apply]
    apply YSeed.ext
    · funext i
      cases g <;> simp
    · rw [SkewExchangeMatrix.tropicalSeed_exchangeMatrix]
      exact g.ySeed_exchangeMatrix _ (SkewExchangeMatrix.tropicalSeed_exchangeMatrix _ _)

/-- Over a field of characteristic zero, words with the same X pullback have identical
tropical actions on every tuple of exponents. -/
theorem tropical_eq_of_xPullback_eq {k : Type*} [Field k] [CharZero k]
    {w : Word B C} {v : Word B D} (h : w.xPullback k = v.xPullback k) :
    Equiv.toFun ((trop).map w) = Equiv.toFun ((trop).map v) := by
  funext b i
  let eval := Qsf.eval (fun j ↦ InfTropical.ofAdd (b j))
  have hs : (⟨Qsf.X, B.val⟩ : YSeed ι (Qsf ι)).map eval = B.tropicalSeed b := by
    ext j <;> simp [eval]
  have hcoeff := (w.xPullback_eq_iff_ySeed_coefficient_eq k v).mp h
  have he (u : SkewExchangeMatrix ι) (p : Word B u) :
      InfTropical.toAdd (eval ((p.ySeed ⟨Qsf.X, B.val⟩).coefficient i)) =
        Equiv.toFun ((trop).map p) b i := by
    have hn := (p.map_ySeed ⟨Qsf.X, B.val⟩ eval).trans
      (hs ▸ p.ySeed_tropicalSeed b)
    simpa only [YSeed.map_coefficient, SkewExchangeMatrix.tropicalSeed_coefficient,
      InfTropical.toAdd_ofAdd] using congrArg (fun s ↦ InfTropical.toAdd (s.coefficient i)) hn
  rw [← he C w, ← he D v, hcoeff]

end Quiver.Path
