/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import QPainleve.Algebra.Cluster.Word.Basic
public import TauCeti.Algebra.Cluster.YSeed.Basic

/-!
# Tropical action of signed cluster words

A signed cluster word transports an integer vector by the tropical cluster `X` formulas.
Mutation is computed using Tau Ceti's coefficient mutation over the min-tropical integers.
The resulting action respects concatenation, reversal and change of labels. It is the integer
calculation used to track candidate boundary valuations through a word.

See Gross, Hacking and Keel, *Birational geometry of cluster algebras*, (1.4), for the
`X` mutation formula with the entry in the mutation column.
-/

public section

namespace QPainleve.Cluster

open Quiver
open scoped Int

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

private instance : TauCeti.CoefficientSemifield (MinTropical ℤ) :=
  { (inferInstance : CommGroup (MinTropical ℤ)),
    (inferInstance : AddCommSemigroup (MinTropical ℤ)),
    (inferInstance : Distrib (MinTropical ℤ)) with }

/-- The `YSeed` formula takes the mutation entry from the row. Negating the skew exchange
matrix puts the original column in that row. -/
private def tropicalSeed (B : SkewExchangeMatrix ι) (b : ι → ℤ) :
    TauCeti.YSeed ι (MinTropical ℤ) :=
  ⟨fun i ↦ MinTropical.trop (b i), (-B).toExchangeMatrix⟩

namespace Generator

/-- The action of one elementary operation on the integer coordinates. -/
def tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → ℤ) : ι → ℤ :=
  match g with
  | .mutate k => fun i ↦ MinTropical.untrop (((tropicalSeed B b).mutation k).coefficient i)
  | .permute σ => b ∘ σ
  | .invert => -b

@[simp]
theorem tropical_mutate_self (B : SkewExchangeMatrix ι) (b : ι → ℤ) (k : ι) :
    (mutate k).tropical B b k = -b k := by
  simp [tropical, tropicalSeed]

/-- The integer mutation formula in a coordinate other than the mutation direction. -/
theorem tropical_mutate_of_ne (B : SkewExchangeMatrix ι) (b : ι → ℤ) {i k : ι} (hi : i ≠ k) :
    (mutate k).tropical B b i =
      b i + (B.matrix i k)⁺ * b k - B.matrix i k * min 0 (b k) := by
  simp [tropical, tropicalSeed, TauCeti.YSeed.mutation_coefficient_of_ne _ hi,
    B.apply_swap i k, sub_eq_add_neg, min_comm (b k) 0]

@[simp]
theorem tropical_permute_apply (B : SkewExchangeMatrix ι) (b : ι → ℤ) (σ : Equiv.Perm ι) (i : ι) :
    (permute σ).tropical B b i = b (σ i) :=
  (rfl)

@[simp]
theorem tropical_invert_apply (B : SkewExchangeMatrix ι) (b : ι → ℤ) (i : ι) :
    invert.tropical B b i = -b i :=
  (rfl)

private theorem tropicalSeed_mutation (B : SkewExchangeMatrix ι) (b : ι → ℤ) (k : ι) :
    tropicalSeed ((mutate k).target B) ((mutate k).tropical B b) =
      (tropicalSeed B b).mutation k := by
  apply TauCeti.YSeed.ext
  · funext i
    simp [tropicalSeed, tropical]
  · simp [tropicalSeed, ← SkewExchangeMatrix.mutate_neg]

/-- The reverse generator acts by the inverse transformation, using the original target matrix
as the source of the reverse. -/
@[simp]
theorem reverse_tropical_tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → ℤ) :
    g.reverse.tropical (g.target B) (g.tropical B b) = b := by
  funext i
  cases g with
  | mutate k =>
    simp only [reverse_mutate]
    calc
      _ = MinTropical.untrop
          ((((tropicalSeed B b).mutation k).mutation k).coefficient i) := by
        rw [tropical, tropicalSeed_mutation]
      _ = b i := by simp [tropicalSeed]
  | permute σ => simp
  | invert => simp

/-- Transporting the labels commutes with the action of a generator on integer coordinates. -/
theorem tropical_reindex (g : Generator ι) (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (b : ι → ℤ) :
    (g.reindex e).tropical (B.reindex e) (b ∘ e.symm) = g.tropical B b ∘ e.symm := by
  funext i
  cases g with
  | mutate k =>
    obtain rfl | hi := eq_or_ne i (e k)
    · simp
    · have hi' : e.symm i ≠ k := fun h ↦ hi (e.symm_apply_eq.mp h)
      simp [tropical_mutate_of_ne, hi, hi']
  | permute σ => simp
  | invert => simp

end Generator

namespace Step

/-- The integer transformation of a signed cluster edge and its inverse. -/
def tropical {B C : SkewExchangeMatrix ι} (s : Step B C) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun := s.generator.tropical B
  invFun := s.generator.reverse.tropical C
  left_inv b := by
    have h := s.generator.reverse_tropical_tropical B b
    rwa [s.target_eq] at h
  right_inv b := by
    have h := s.generator.reverse.reverse_tropical_tropical C b
    rw [Generator.reverse_reverse] at h
    have hB := Step.target_eq (Quiver.reverse (a := B) (b := C) s)
    rw [Step.reverse_generator] at hB
    rwa [hB] at h

@[simp]
theorem tropical_apply {B C : SkewExchangeMatrix ι} (s : Step B C) (b : ι → ℤ) :
    s.tropical b = s.generator.tropical B b :=
  (rfl)

@[simp]
theorem tropical_symm_apply {B C : SkewExchangeMatrix ι} (s : Step B C) (b : ι → ℤ) :
    s.tropical.symm b = s.generator.reverse.tropical C b :=
  (rfl)

@[simp]
theorem tropical_reverse {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    Step.tropical (Quiver.reverse s) = (Step.tropical s).symm := by
  ext b i
  simp

end Step

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve.Cluster

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {B C D : SkewExchangeMatrix ι}

/-- Evaluate a signed cluster word on integer coordinates by performing each operation in
execution order. -/
def tropical : ∀ {C : SkewExchangeMatrix ι}, Path B C → (ι → ℤ) ≃ (ι → ℤ)
  | _, .nil => Equiv.refl _
  | _, .cons w s => (tropical w).trans (Step.tropical s)

@[simp]
theorem tropical_nil : (Path.nil : Word B B).tropical = Equiv.refl _ :=
  (rfl)

@[simp]
theorem tropical_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).tropical = w.tropical.trans (Step.tropical s) :=
  (rfl)

@[simp]
theorem tropical_toPath (s : B ⟶ C) : s.toPath.tropical = Step.tropical s := by
  simp [Hom.toPath]

/-- Evaluation of concatenated words is composition in execution order. -/
@[simp]
theorem tropical_comp (w : Word B C) (v : Word C D) :
    (w.comp v).tropical = w.tropical.trans v.tropical := by
  induction v with
  | nil => simp
  | cons _ _ ih => simp [ih, Equiv.trans_assoc]

/-- Reversing the word inverts its integer transformation. -/
@[simp]
theorem tropical_reverse (w : Word B C) :
    w.reverse.tropical = w.tropical.symm := by
  induction w with
  | nil => rfl
  | cons _ _ ih =>
    simp [ih, Equiv.symm_trans]

/-- Integer evaluation commutes with changing labels on the entire word. -/
theorem tropical_reindex (e : ι ≃ κ) (w : Word B C) (b : ι → ℤ) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).tropical (b ∘ e.symm) =
      w.tropical b ∘ e.symm := by
  induction w with
  | nil => simp
  | cons _ s ih =>
    simp [ih, Generator.tropical_reindex]

end Quiver.Path
