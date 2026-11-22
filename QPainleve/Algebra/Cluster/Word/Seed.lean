/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Basic
public import QPainleve.Algebra.Cluster.YSeed.Inversion
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Y-seed evaluation of signed cluster words

Evaluate a typed word by applying Tau Ceti's Y-seed mutation and relabeling, and signed
inversion, in execution order. The endpoint matrix agrees with the word's target when the
initial seed has the source matrix. Coefficient specialization commutes with evaluation.
-/

public section

open CategoryTheory Quiver TauCeti

variable {ι κ P Q : Type*} [DecidableEq ι] [CoefficientSemifield P] [CoefficientSemifield Q]

namespace QPainleve.Cluster.Generator

/-- Apply a signed cluster generator to the coefficients and matrix of a Y-seed. -/
def ySeed (g : Generator ι) (s : YSeed ι P) : YSeed ι P :=
  match g with
  | .mutate p => s.mutation p
  | .permute σ => YSeed.reindex σ.symm s
  | .invert => s.invert

@[simp]
theorem ySeed_mutate (p : ι) (s : YSeed ι P) :
    (mutate p).ySeed s = s.mutation p :=
  (rfl)

@[simp]
theorem ySeed_permute (σ : Equiv.Perm ι) (s : YSeed ι P) :
    (permute σ).ySeed s = YSeed.reindex σ.symm s :=
  (rfl)

@[simp]
theorem ySeed_invert (s : YSeed ι P) : invert.ySeed s = s.invert :=
  (rfl)

/-- For a seed with the source exchange matrix, the new matrix is the typed target. -/
theorem ySeed_exchangeMatrix (g : Generator ι) (s : YSeed ι P) {B : SkewExchangeMatrix ι}
    (hs : s.exchangeMatrix = B.val) : (g.ySeed s).exchangeMatrix = (g.target B).val := by
  cases g with
  | mutate | permute => simp [hs]
  | invert =>
    apply ExchangeMatrix.ext
    · simp [hs, SkewExchangeMatrix.val_matrix]
    · simpa [hs] using B.property.trans (-B).property.symm

/-- The reverse generator undoes the original operation on the Y-seed. -/
@[simp]
theorem reverse_ySeed_ySeed (g : Generator ι) (s : YSeed ι P) :
    g.reverse.ySeed (g.ySeed s) = s := by
  cases g <;> simp

/-- Specializing coefficients commutes with the action of each generator. -/
@[simp]
theorem map_ySeed (g : Generator ι) (s : YSeed ι P) (f : CoefficientSemifieldHom P Q) :
    (g.ySeed s).map f = g.ySeed (s.map f) := by
  cases g <;> simp

/-- The seed action intertwines a change of labels on the generator. -/
theorem ySeed_reindex [DecidableEq κ] (g : Generator ι) (e : ι ≃ κ) (s : YSeed ι P) :
    (g.reindex e).ySeed (YSeed.reindex e s) = YSeed.reindex e (g.ySeed s) := by
  cases g with
  | mutate => simp [YSeed.mutation_reindex]
  | permute σ =>
    simp only [reindex_permute, ySeed_permute, YSeed.reindex_reindex]
    apply congrArg (fun f : ι ≃ κ ↦ YSeed.reindex f s)
    apply Equiv.ext
    intro i
    simp
  | invert => simp

end QPainleve.Cluster.Generator

namespace Quiver.Path

open QPainleve.Cluster

variable {B C D : SkewExchangeMatrix ι}

private def ySeedPrefunctor (ι : Type*) [DecidableEq ι] (P : Type*) [CoefficientSemifield P] :
    SkewExchangeMatrix ι ⥤q Type _ where
  obj _ := YSeed ι P
  map e := ↾(Step.generator e).ySeed

/-- Evaluate a signed word on a Y-seed by applying its generators in execution order. -/
def ySeed (w : Word B C) (s : YSeed ι P) : YSeed ι P :=
  (Paths.lift (ySeedPrefunctor ι P)).map w s

@[simp]
theorem ySeed_nil (s : YSeed ι P) :
    (Path.nil : Word B B).ySeed s = s :=
  (rfl)

@[simp]
theorem ySeed_toPath (e : B ⟶ C) (s : YSeed ι P) :
    e.toPath.ySeed s = (Step.generator e).ySeed s := by
  unfold ySeed
  rw [Paths.lift_toPath]
  rfl

/-- Evaluating a concatenation applies the first word before the second word. -/
@[simp]
theorem ySeed_comp (w : Word B C) (v : Word C D) (s : YSeed ι P) :
    (w.comp v).ySeed s = v.ySeed (w.ySeed s) := by
  unfold ySeed
  exact congrArg (fun f : YSeed ι P ⟶ YSeed ι P ↦ f s)
    ((Paths.lift (ySeedPrefunctor ι P)).map_comp w v)

@[simp]
theorem ySeed_cons (w : Word B C) (e : C ⟶ D) (s : YSeed ι P) :
    (w.cons e).ySeed s = (Step.generator e).ySeed (w.ySeed s) := by
  rw [← Path.comp_toPath_eq_cons, ySeed_comp, ySeed_toPath]

/-- For the given source matrix, evaluation has the prescribed target exchange matrix. -/
theorem ySeed_exchangeMatrix (w : Word B C) (s : YSeed ι P)
    (hs : s.exchangeMatrix = B.val) : (w.ySeed s).exchangeMatrix = C.val := by
  induction w with
  | nil => simpa using hs
  | cons w e ih =>
    rw [ySeed_cons, (Step.generator e).ySeed_exchangeMatrix _ ih, Step.target_eq e]

/-- The reversed word undoes evaluation. -/
@[simp]
theorem ySeed_reverse_ySeed (w : Word B C) (s : YSeed ι P) :
    w.reverse.ySeed (w.ySeed s) = s := by
  induction w with
  | nil => simp [Path.reverse]
  | cons w e ih => simp [Path.reverse, ih]

/-- Specializing coefficients commutes with evaluation of any signed word. -/
@[simp]
theorem map_ySeed (w : Word B C) (s : YSeed ι P) (f : CoefficientSemifieldHom P Q) :
    (w.ySeed s).map f = w.ySeed (s.map f) := by
  induction w with
  | nil => simp
  | cons w e ih => simp [ih]

/-- Relabeling a signed word intertwines evaluation with relabeling its seeds. -/
theorem ySeed_reindex [DecidableEq κ] (e : ι ≃ κ) (w : Word B C) (s : YSeed ι P) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).ySeed (YSeed.reindex e s) =
      YSeed.reindex e (w.ySeed s) := by
  induction w with
  | nil => rfl
  | cons w a ih =>
    simp [Prefunctor.mapPath_cons, ih, Generator.ySeed_reindex]

end Quiver.Path
