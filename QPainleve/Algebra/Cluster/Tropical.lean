/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.SingleObj
public import QPainleve.Algebra.Cluster.Word.Basic
public import TauCeti.Algebra.Cluster.YSeed.Basic

/-!
# Tropical action of signed cluster words

A signed cluster word transports an integer vector by the tropical cluster `X` formulas.
Mutation and relabeling use Tau Ceti's `YSeed` operations over the min-tropical integers.
Mathlib's `CategoryTheory.Paths.lift` composes the edge transformations in execution order.
The resulting action respects concatenation, reversal and change of labels. It is the integer
calculation used to track candidate boundary valuations through a word.

See Gross, Hacking and Keel, *Birational geometry of cluster algebras*, (1.4), for the
`X` mutation formula with the entry in the mutation column.
-/

public section

namespace QPainleve.Cluster

open CategoryTheory Quiver
open scoped Int

variable {ι κ : Type*}

private instance : TauCeti.CoefficientSemifield (MinTropical ℤ) :=
  { (inferInstance : CommGroup (MinTropical ℤ)),
    (inferInstance : AddCommSemigroup (MinTropical ℤ)),
    (inferInstance : Distrib (MinTropical ℤ)) with }

/-- Interpret a vector of integer coordinates as tropical coefficients on the native seed. -/
private def tropicalSeed (B : SkewExchangeMatrix ι) (b : ι → ℤ) :
    TauCeti.YSeed ι (MinTropical ℤ) :=
  ⟨fun i ↦ MinTropical.trop (b i), B.val⟩

private theorem tropicalSeed_reindex (B : SkewExchangeMatrix ι) (b : ι → ℤ) (e : ι ≃ κ) :
    tropicalSeed (B.reindex e) (b ∘ e.symm) = (tropicalSeed B b).reindex e := by
  refine TauCeti.YSeed.ext (funext fun i ↦ ?_) (by simp [tropicalSeed])
  simp [tropicalSeed]

variable [DecidableEq ι] [DecidableEq κ]

namespace Generator

/-- The action of one elementary operation on the integer coordinates. -/
def tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → ℤ) : ι → ℤ :=
  match g with
  | .mutate k => fun i ↦ MinTropical.untrop (((tropicalSeed B b).mutation k).coefficient i)
  | .permute σ => fun i ↦ MinTropical.untrop (((tropicalSeed B b).reindex σ.symm).coefficient i)
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
    SkewExchangeMatrix.val_matrix_apply_swap, sub_eq_add_neg, min_comm (b k) 0]

@[simp]
theorem tropical_permute_apply (B : SkewExchangeMatrix ι) (b : ι → ℤ) (σ : Equiv.Perm ι) (i : ι) :
    (permute σ).tropical B b i = b (σ i) := by
  simp [tropical, tropicalSeed]

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
  · simp [tropicalSeed]

/-- The reverse generator acts by the inverse transformation, using the original target matrix
as the source of the reverse. -/
@[simp]
theorem reverse_tropical_tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → ℤ) :
    g.reverse.tropical (g.target B) (g.tropical B b) = b := by
  funext i
  cases g with
  | mutate k =>
    rw [reverse_mutate, tropical, tropicalSeed_mutation]
    simp [tropicalSeed]
  | permute σ => simp
  | invert => simp

/-- Transporting the labels commutes with the action of a generator on integer coordinates. -/
theorem tropical_reindex (g : Generator ι) (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (b : ι → ℤ) :
    (g.reindex e).tropical (B.reindex e) (b ∘ e.symm) = g.tropical B b ∘ e.symm := by
  funext i
  cases g with
  | mutate k =>
    simp only [reindex_mutate, tropical, tropicalSeed_reindex, TauCeti.YSeed.mutation_reindex,
      TauCeti.YSeed.reindex_coefficient, Function.comp_apply]
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

/-- The tropical permutations on signed cluster edges. The path-category lift evaluates
words by composing these permutations in execution order. -/
def tropicalPrefunctor (ι : Type*) [DecidableEq ι] :
    SkewExchangeMatrix ι ⥤q CategoryTheory.SingleObj (Equiv.Perm (ι → ℤ)) where
  obj _ := CategoryTheory.SingleObj.star _
  map := Step.tropical

@[simp]
theorem tropicalPrefunctor_map {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    (tropicalPrefunctor ι).map s = Step.tropical s := (rfl)

variable {B C : SkewExchangeMatrix ι}

/-- Reversing the word inverts its integer transformation. -/
@[simp]
theorem tropical_reverse (w : Word B C) :
    (Paths.lift (tropicalPrefunctor ι)).map w.reverse =
      CategoryTheory.inv ((Paths.lift (tropicalPrefunctor ι)).map w) := by
  induction w with
  | nil =>
    simp only [Path.reverse, Paths.lift_nil, SingleObj.inv_as_inv, SingleObj.id_as_one]
    rfl
  | cons w s ih =>
    refine ((Paths.lift (tropicalPrefunctor ι)).map_comp (Quiver.reverse s).toPath
      w.reverse).trans ?_
    simp only [Paths.lift_toPath, tropicalPrefunctor_map, ih, Paths.lift_cons,
      IsIso.inv_comp, SingleObj.inv_as_inv, Step.tropical_reverse]
    rfl

/-- Integer evaluation commutes with changing labels on the entire word. -/
theorem tropical_reindex (e : ι ≃ κ) (w : Word B C) (b : ι → ℤ) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor κ)).map
        ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w)) (b ∘ e.symm) =
      Equiv.toFun ((Paths.lift (tropicalPrefunctor ι)).map w) b ∘ e.symm := by
  induction w with
  | nil => rfl
  | cons w s ih =>
    have hs (x : ι → ℤ) :
        Step.tropical ((SkewExchangeMatrix.reindexPrefunctor e).map s) (x ∘ e.symm) =
          Step.tropical s x ∘ e.symm := by
      simpa using s.generator.tropical_reindex _ e x
    simp only [Prefunctor.mapPath_cons, Paths.lift_cons, tropicalPrefunctor_map,
      SingleObj.comp_as_mul]
    exact (congrArg (Step.tropical ((SkewExchangeMatrix.reindexPrefunctor e).map s)) ih).trans
      (hs _)

end QPainleve.Cluster
