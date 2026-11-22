/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.SingleObj
public import QPainleve.Algebra.Cluster.Word.Basic
public import TauCeti.Algebra.Cluster.CoefficientSemifield.Tropical
public import TauCeti.Algebra.Cluster.YSeed.Basic

import Mathlib.Tactic.Abel

/-!
# Tropical action of signed cluster words

A signed cluster word transports exponents by the tropical cluster `X` formulas.
Mutation and relabeling use Tau Ceti's `YSeed` operations over `InfTropical`.
Integer exponents encode one candidate boundary valuation, and finitely supported integer
exponents encode several valuations at once.
Mathlib's `CategoryTheory.Paths.lift` composes the edge transformations in execution order.
The resulting action respects concatenation, reversal and change of labels. It is the integer
calculation used to track candidate boundary valuations through a word.

See Gross, Hacking and Keel, *Birational geometry of cluster algebras*, (1.4), for the
`X` mutation formula with the entry in the mutation column. Simultaneous inversion uses
`TauCeti.CoefficientSemifield.inv_add_inv`.
-/

public section

namespace QPainleve.Cluster

open CategoryTheory Quiver
open TauCeti (InfTropical YSeed)
open scoped Int

variable {ι κ A : Type*} [AddCommGroup A] [SemilatticeInf A] [IsOrderedAddMonoid A]

namespace SkewExchangeMatrix

/-- Equip a skew exchange matrix with `InfTropical` coefficients given by the exponents `b`. -/
def tropicalSeed (B : SkewExchangeMatrix ι) (b : ι → A) : YSeed ι (InfTropical A) :=
  ⟨fun i ↦ InfTropical.ofAdd (b i), B.val⟩

@[simp]
theorem tropicalSeed_coefficient (B : SkewExchangeMatrix ι) (b : ι → A) (i : ι) :
    (B.tropicalSeed b).coefficient i = InfTropical.ofAdd (b i) :=
  (rfl)

@[simp]
theorem tropicalSeed_exchangeMatrix (B : SkewExchangeMatrix ι) (b : ι → A) :
    (B.tropicalSeed b).exchangeMatrix = B.val :=
  (rfl)

/-- Relabeling the exchange matrix and the exponents relabels the associated seed. -/
@[simp]
theorem tropicalSeed_reindex (B : SkewExchangeMatrix ι) (b : ι → A) (e : ι ≃ κ) :
    (B.reindex e).tropicalSeed (b ∘ e.symm) = (B.tropicalSeed b).reindex e := by
  ext i <;> simp [Function.comp_def]

end SkewExchangeMatrix

variable [DecidableEq ι] [DecidableEq κ]

namespace Generator

/-- The action of one elementary operation on tropical exponents. -/
def tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → A) : ι → A :=
  match g with
  | .mutate k => fun i ↦ InfTropical.toAdd (((B.tropicalSeed b).mutation k).coefficient i)
  | .permute σ => fun i ↦ InfTropical.toAdd (((B.tropicalSeed b).reindex σ.symm).coefficient i)
  | .invert => -b

@[simp]
theorem tropical_mutate_self (B : SkewExchangeMatrix ι) (b : ι → A) (k : ι) :
    (mutate k).tropical B b k = -b k := by
  simp [tropical]

/-- The tropical mutation formula away from the mutation direction. -/
theorem tropical_mutate_of_ne_smul (B : SkewExchangeMatrix ι) (b : ι → A) {i k : ι}
    (hi : i ≠ k) :
    (mutate k).tropical B b i =
      b i + (B.matrix i k)⁺ • b k - B.matrix i k • (0 ⊓ b k) := by
  simp [tropical, YSeed.mutation_coefficient_of_ne _ hi,
    SkewExchangeMatrix.val_matrix_apply_swap, sub_eq_add_neg, inf_comm (b k) 0]

/-- The integer mutation formula in a coordinate other than the mutation direction. -/
theorem tropical_mutate_of_ne (B : SkewExchangeMatrix ι) (b : ι → ℤ) {i k : ι} (hi : i ≠ k) :
    (mutate k).tropical B b i =
      b i + (B.matrix i k)⁺ * b k - B.matrix i k * min 0 (b k) := by
  simpa only [smul_eq_mul] using tropical_mutate_of_ne_smul B b hi

@[simp]
theorem tropical_permute_apply (B : SkewExchangeMatrix ι) (b : ι → A) (σ : Equiv.Perm ι) (i : ι) :
    (permute σ).tropical B b i = b (σ i) := by
  simp [tropical]

@[simp]
theorem tropical_invert_apply (B : SkewExchangeMatrix ι) (b : ι → A) (i : ι) :
    invert.tropical B b i = -b i :=
  (rfl)

/-- Negating the exchange matrix and input exponents negates the output exponents. -/
@[simp]
theorem tropical_neg (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → A) :
    g.tropical (-B) (-b) = -g.tropical B b := by
  funext i
  cases g with
  | mutate k =>
    obtain rfl | hi := eq_or_ne i k
    · simp
    have hInf : 0 ⊓ -b k = (0 ⊓ b k) - b k := by
      simpa using congrArg InfTropical.toAdd
        (TauCeti.CoefficientSemifield.inv_add_inv (1 : InfTropical A) (InfTropical.ofAdd (b k)))
    have hPos : (-(B.matrix i k))⁺ + B.matrix i k = (B.matrix i k)⁺ := by
      rw [posPart_neg]
      exact eq_sub_iff_add_eq'.mp (posPart_sub_negPart (B.matrix i k)).symm
    simp only [tropical_mutate_of_ne_smul _ _ hi, Pi.neg_apply, SkewExchangeMatrix.neg_matrix,
      Matrix.neg_apply]
    rw [hInf, ← hPos]
    simp only [smul_neg, neg_smul, smul_sub, add_smul]
    abel
  | permute σ => simp
  | invert => simp

/-- The exponent transformation of a mutation recovers native Y-seed mutation. -/
@[simp]
theorem tropicalSeed_mutation (B : SkewExchangeMatrix ι) (b : ι → A) (k : ι) :
    (B.mutate k).tropicalSeed ((mutate k).tropical B b) =
      (B.tropicalSeed b).mutation k := by
  apply YSeed.ext
  · funext i
    simp [tropical]
  · simp

/-- The reverse generator acts by the inverse transformation, using the original target matrix
as the source of the reverse. -/
@[simp]
theorem reverse_tropical_tropical (g : Generator ι) (B : SkewExchangeMatrix ι) (b : ι → A) :
    g.reverse.tropical (g.target B) (g.tropical B b) = b := by
  funext i
  cases g with
  | mutate k =>
    rw [reverse_mutate, tropical, target_mutate, tropicalSeed_mutation]
    simp
  | permute σ => simp
  | invert => simp

/-- Transporting the labels commutes with the action of a generator on exponents. -/
theorem tropical_reindex (g : Generator ι) (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (b : ι → A) :
    (g.reindex e).tropical (B.reindex e) (b ∘ e.symm) = g.tropical B b ∘ e.symm := by
  funext i
  cases g with
  | mutate k =>
    simp only [reindex_mutate, tropical, SkewExchangeMatrix.tropicalSeed_reindex,
      YSeed.mutation_reindex, YSeed.reindex_coefficient, Function.comp_apply]
  | permute σ => simp
  | invert => simp

end Generator

namespace Step

/-- The tropical exponent transformation of a signed cluster edge and its inverse. -/
def tropical {B C : SkewExchangeMatrix ι} (s : Step B C) : (ι → A) ≃ (ι → A) where
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
theorem tropical_apply {B C : SkewExchangeMatrix ι} (s : Step B C) (b : ι → A) :
    s.tropical b = s.generator.tropical B b :=
  (rfl)

@[simp]
theorem tropical_symm_apply {B C : SkewExchangeMatrix ι} (s : Step B C) (b : ι → A) :
    s.tropical.symm b = s.generator.reverse.tropical C b :=
  (rfl)

@[simp]
theorem tropical_reverse {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    Step.tropical (A := A) (Quiver.reverse s) = (Step.tropical s).symm := by
  ext b i
  simp

end Step

/-- The tropical permutations on signed cluster edges. The path-category lift evaluates
words by composing these permutations in execution order. -/
def tropicalPrefunctor (ι : Type*) [DecidableEq ι] :
    SkewExchangeMatrix ι ⥤q CategoryTheory.SingleObj (Equiv.Perm (ι → A)) where
  obj _ := CategoryTheory.SingleObj.star _
  map := Step.tropical

@[simp]
theorem tropicalPrefunctor_map {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    (tropicalPrefunctor (A := A) ι).map s = Step.tropical s := (rfl)

variable {B C D : SkewExchangeMatrix ι}

/-- Append an edge to a word by applying its tropical transformation to the word's output. -/
theorem tropical_map_cons_apply (w : Word B C) (s : C ⟶ D) (b : ι → A) :
    DFunLike.coe (F := Equiv.Perm (ι → A))
        ((Paths.lift (tropicalPrefunctor (A := A) ι)).map (w.cons s)) b =
      Step.tropical s (DFunLike.coe (F := Equiv.Perm (ι → A))
        ((Paths.lift (tropicalPrefunctor (A := A) ι)).map w) b) := by
  rw [Paths.lift_cons, tropicalPrefunctor_map, SingleObj.comp_as_mul]
  rfl

/-- Reversing the word inverts its exponent transformation. -/
@[simp]
theorem tropical_reverse (w : Word B C) :
    (Paths.lift (tropicalPrefunctor (A := A) ι)).map w.reverse =
      CategoryTheory.inv ((Paths.lift (tropicalPrefunctor (A := A) ι)).map w) := by
  induction w with
  | nil =>
    simp only [Path.reverse, Paths.lift_nil, SingleObj.inv_as_inv, SingleObj.id_as_one]
    rfl
  | cons w s ih =>
    refine ((Paths.lift (tropicalPrefunctor (A := A) ι)).map_comp (Quiver.reverse s).toPath
      w.reverse).trans ?_
    simp only [Paths.lift_toPath, tropicalPrefunctor_map, ih, Paths.lift_cons,
      IsIso.inv_comp, SingleObj.inv_as_inv, Step.tropical_reverse]
    rfl

/-- Tropical exponent evaluation commutes with changing labels on the entire word. -/
theorem tropical_reindex (e : ι ≃ κ) (w : Word B C) (b : ι → A) :
    Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := A) κ)).map
        ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w)) (b ∘ e.symm) =
      Equiv.toFun ((Paths.lift (tropicalPrefunctor (A := A) ι)).map w) b ∘ e.symm := by
  induction w with
  | nil => rfl
  | cons w s ih =>
    have hs (x : ι → A) :
        Step.tropical ((SkewExchangeMatrix.reindexPrefunctor e).map s) (x ∘ e.symm) =
          Step.tropical s x ∘ e.symm := by
      simpa using s.generator.tropical_reindex _ e x
    simp only [Equiv.toFun_as_coe, Prefunctor.mapPath_cons, tropical_map_cons_apply]
    exact (congrArg (Step.tropical ((SkewExchangeMatrix.reindexPrefunctor e).map s)) ih).trans
      (hs _)

end QPainleve.Cluster
