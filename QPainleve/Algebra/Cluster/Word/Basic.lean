/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Combinatorics.Quiver.Symmetric
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.Tactic.LinearCombination

/-!
# Signed cluster words

The vertices are the square, unit-symmetrizer subtype of `TauCeti.ExchangeMatrix`. Its native
matrix is `-ε`, so its mutation row is the column used in the cluster `X` formulas. An edge
records a mutation, a permutation of the labels, or simultaneous sign reversal. Mathlib's quiver
paths retain the source and target of a word under concatenation, reversal, and changes of labels.
Two generators with the same endpoints still record distinct operations.

The matrix action uses Tau Ceti's `ExchangeMatrix.mutation` and `ExchangeMatrix.reindex`.
For mutation and permutations see Fock and Goncharov, *Cluster ensembles, quantization and
the dilogarithm*, §1.2.2. For the operation adjoining sign reversal see Bershtein, Gavrylenko
and Marshakov, *Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1.
-/

public section

namespace QPainleve.Cluster

open scoped Int
open Quiver

variable {ι κ ρ : Type*}

/-- A square Tau Ceti exchange matrix with constant symmetrizer one. Its underlying matrix
is `-ε` in the cluster `X` convention. -/
abbrev SkewExchangeMatrix (ι : Type*) :=
  {B : TauCeti.ExchangeMatrix (Function.Embedding.refl ι) // B.symmetrizer = fun _ ↦ 1}

namespace SkewExchangeMatrix

/-- The cluster `X` exchange entries `ε`, the negative of the native matrix. -/
def matrix (B : SkewExchangeMatrix ι) : Matrix ι ι ℤ := -B.val.matrix

/-- The native exchange matrix is the negative of the cluster `X` exchange matrix. -/
theorem val_matrix (B : SkewExchangeMatrix ι) : B.val.matrix = -B.matrix := by
  simp [matrix]

/-- The native mutation row agrees with the cluster `X` mutation column. -/
theorem val_matrix_apply_swap (B : SkewExchangeMatrix ι) (i j : ι) :
    B.val.matrix j i = B.matrix i j := by
  simpa [B.property, matrix] using B.val.symmetrizer_mul_matrix j i

/-- The cluster `X` entries have unit skew-symmetrizer. -/
theorem isSkewSymmetrizer (B : SkewExchangeMatrix ι) : B.matrix.IsSkewSymmetrizer (fun _ ↦ 1) := by
  simpa only [matrix, Function.Embedding.coe_refl, Matrix.submatrix_id_id, B.property]
    using B.val.isSkewSymmetrizer.neg

/-- Interpret skew-symmetric cluster `X` entries as a native exchange matrix. -/
def ofMatrix (ε : Matrix ι ι ℤ) (h : ε.IsSkewSymmetrizer (fun _ ↦ 1)) : SkewExchangeMatrix ι :=
  ⟨⟨-ε, fun _ ↦ 1, by
    simpa only [Function.Embedding.coe_refl, Matrix.submatrix_id_id] using h.neg⟩, rfl⟩

@[simp]
theorem val_ofMatrix_matrix (ε : Matrix ι ι ℤ) (h : ε.IsSkewSymmetrizer (fun _ ↦ 1)) :
    (ofMatrix ε h).val.matrix = -ε :=
  (rfl)

@[simp]
theorem matrix_ofMatrix (ε : Matrix ι ι ℤ) (h : ε.IsSkewSymmetrizer (fun _ ↦ 1)) :
    (ofMatrix ε h).matrix = ε := by
  simp [matrix]

/-- The cluster `X` entries determine a unit-symmetrizer exchange matrix. -/
@[ext]
theorem ext {B C : SkewExchangeMatrix ι} (h : B.matrix = C.matrix) : B = C :=
  Subtype.ext <| TauCeti.ExchangeMatrix.ext
    (by simpa only [val_matrix] using congrArg Neg.neg h) (B.property.trans C.property.symm)

@[simp]
theorem ofMatrix_matrix (B : SkewExchangeMatrix ι) : ofMatrix B.matrix B.isSkewSymmetrizer = B :=
  ext (matrix_ofMatrix _ _)

/-- Skew-symmetry interchanges the two entries with a sign change. -/
theorem apply_swap (B : SkewExchangeMatrix ι) (i j : ι) : B.matrix j i = -B.matrix i j := by
  simpa using B.isSkewSymmetrizer.mul_apply j i

@[simp]
theorem apply_diag (B : SkewExchangeMatrix ι) (i : ι) : B.matrix i i = 0 :=
  B.isSkewSymmetrizer.apply_self i

instance : Neg (SkewExchangeMatrix ι) where
  neg B :=
    ⟨{ B.val with
        matrix := -B.val.matrix
        isSkewSymmetrizer := B.val.isSkewSymmetrizer.neg },
      B.property⟩

@[simp]
theorem neg_matrix (B : SkewExchangeMatrix ι) : (-B).matrix = -B.matrix :=
  (rfl)

@[simp]
theorem neg_neg (B : SkewExchangeMatrix ι) : -(-B) = B := by
  apply ext
  simp

/-- Transport a matrix to new labels using the same equivalence for rows and columns. -/
def reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) : SkewExchangeMatrix κ :=
  ⟨TauCeti.ExchangeMatrix.reindex (row' := Function.Embedding.refl κ) e e (by simp) B.val,
    by simp [B.property, Function.comp_def]⟩

@[simp]
theorem val_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (B.reindex e).val =
      TauCeti.ExchangeMatrix.reindex (row' := Function.Embedding.refl κ) e e (by simp) B.val :=
  (rfl)

@[simp]
theorem reindex_matrix (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (B.reindex e).matrix = B.matrix.submatrix e.symm e.symm := by
  simp only [matrix, val_reindex, TauCeti.ExchangeMatrix.reindex_matrix]
  rfl

@[simp]
theorem reindex_refl (B : SkewExchangeMatrix ι) : B.reindex (Equiv.refl ι) = B := by
  apply Subtype.ext
  simp

@[simp]
theorem reindex_trans (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (f : κ ≃ ρ) :
    (B.reindex e).reindex f = B.reindex (e.trans f) := by
  apply Subtype.ext
  simpa only [val_reindex, Equiv.trans_apply] using Equiv.congr_fun
    (TauCeti.ExchangeMatrix.reindex_trans (row := Function.Embedding.refl ι)
      (row' := Function.Embedding.refl κ) (row'' := Function.Embedding.refl ρ)
      e e (by simp) f f (by simp)) B.val

@[simp]
theorem reindex_neg (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (-B).reindex e = -(B.reindex e) := by
  apply ext
  ext i j
  simp

variable [DecidableEq ι] [DecidableEq κ]

/-- Mutate the exchange matrix at label `k`. -/
def mutate (B : SkewExchangeMatrix ι) (k : ι) : SkewExchangeMatrix ι :=
  ⟨B.val.mutation k, (TauCeti.ExchangeMatrix.mutation_symmetrizer B.val k).trans B.property⟩

@[simp]
theorem val_mutate (B : SkewExchangeMatrix ι) (k : ι) : (B.mutate k).val = B.val.mutation k :=
  (rfl)

@[simp]
theorem mutate_matrix (B : SkewExchangeMatrix ι) (k : ι) :
    (B.mutate k).matrix = TauCeti.matrixMutation (Function.Embedding.refl ι) B.matrix k := by
  simp only [matrix, val_mutate, TauCeti.ExchangeMatrix.mutation_matrix,
    TauCeti.matrixMutation_neg]

/-- The exchange entry away from the mutation row and column, in the positive-part convention
for cluster `X` mutation. -/
theorem mutate_matrix_apply_of_ne (B : SkewExchangeMatrix ι) {i j k : ι}
    (hi : i ≠ k) (hj : j ≠ k) :
    (B.mutate k).matrix i j = B.matrix i j + (B.matrix i k)⁺ * B.matrix k j +
      B.matrix i k * (-B.matrix k j)⁺ := by
  rw [mutate_matrix, TauCeti.matrixMutation_refl_apply_of_ne hi hj, posPart_neg]
  linear_combination (B.matrix i k)⁺ * posPart_sub_negPart (B.matrix k j) +
    (B.matrix k j)⁻ * posPart_sub_negPart (B.matrix i k)

@[simp]
theorem mutate_mutate (B : SkewExchangeMatrix ι) (k : ι) : (B.mutate k).mutate k = B := by
  apply Subtype.ext
  simp

@[simp]
theorem mutate_neg (B : SkewExchangeMatrix ι) (k : ι) : (-B).mutate k = -(B.mutate k) := by
  apply SkewExchangeMatrix.ext
  simp

@[simp]
theorem mutate_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (k : ι) :
    (B.reindex e).mutate (e k) = (B.mutate k).reindex e := by
  apply Subtype.ext
  simpa only [val_mutate, val_reindex] using
    B.val.mutation_reindex (row' := Function.Embedding.refl κ) e e (by simp) k

end SkewExchangeMatrix

/-- The generators of signed cluster words on a label type. In a permutation, the
permutation sends each target label to its source label. -/
inductive Generator (ι : Type*) where
  /-- Mutation in a single direction. -/
  | mutate (k : ι)
  /-- Relabeling by a permutation from target labels to source labels. -/
  | permute (σ : Equiv.Perm ι)
  /-- Negation of the exchange matrix and inversion of all `X` coordinates. -/
  | invert

namespace Generator

/-- Reverse a generator. Mutation and global inversion are self-inverse, and the reverse
of a permutation uses its inverse. -/
def reverse : Generator ι → Generator ι
  | .mutate k => .mutate k
  | .permute σ => .permute σ.symm
  | .invert => .invert

@[simp] theorem reverse_mutate (k : ι) : (mutate k).reverse = mutate k :=
  (rfl)

@[simp] theorem reverse_permute (σ : Equiv.Perm ι) : (permute σ).reverse = permute σ.symm :=
  (rfl)

@[simp] theorem reverse_invert : (invert : Generator ι).reverse = invert :=
  (rfl)

@[simp]
theorem reverse_reverse (g : Generator ι) : g.reverse.reverse = g := by
  cases g <;> simp

/-- Transport a generator from the old label type to the new one. -/
def reindex (e : ι ≃ κ) : Generator ι → Generator κ
  | .mutate k => .mutate (e k)
  | .permute σ => .permute ((e.symm.trans σ).trans e)
  | .invert => .invert

@[simp] theorem reindex_mutate (e : ι ≃ κ) (k : ι) :
    (mutate k).reindex e = mutate (e k) :=
  (rfl)

@[simp] theorem reindex_permute (e : ι ≃ κ) (σ : Equiv.Perm ι) :
    (permute σ).reindex e = permute ((e.symm.trans σ).trans e) :=
  (rfl)

@[simp] theorem reindex_invert (e : ι ≃ κ) : invert.reindex e = (invert : Generator κ) :=
  (rfl)

@[simp]
theorem reindex_refl (g : Generator ι) : g.reindex (Equiv.refl ι) = g := by
  cases g <;> simp

@[simp]
theorem reindex_trans (g : Generator ι) (e : ι ≃ κ) (f : κ ≃ ρ) :
    (g.reindex e).reindex f = g.reindex (e.trans f) := by
  cases g <;> simp [Equiv.symm_trans, Equiv.trans_assoc]

@[simp]
theorem reindex_reverse (g : Generator ι) (e : ι ≃ κ) :
    g.reverse.reindex e = (g.reindex e).reverse := by
  cases g <;> simp [Equiv.symm_trans, Equiv.trans_assoc]

/-- The contribution of a generator to a word's inversion count. -/
def inversionCount : Generator ι → ℕ
  | .mutate _ | .permute _ => 0
  | .invert => 1

@[simp]
theorem inversionCount_mutate (p : ι) : (mutate p).inversionCount = 0 :=
  (rfl)

@[simp]
theorem inversionCount_permute (σ : Equiv.Perm ι) : (permute σ).inversionCount = 0 :=
  (rfl)

@[simp]
theorem inversionCount_invert : (invert : Generator ι).inversionCount = 1 :=
  (rfl)

@[simp]
theorem inversionCount_eq_zero (g : Generator ι) : g.inversionCount = 0 ↔ g ≠ .invert := by
  cases g <;> simp

@[simp]
theorem inversionCount_reverse (g : Generator ι) : g.reverse.inversionCount = g.inversionCount := by
  cases g <;> simp

@[simp]
theorem inversionCount_reindex {κ : Type*} (g : Generator ι) (e : ι ≃ κ) :
    (g.reindex e).inversionCount = g.inversionCount := by
  cases g <;> simp

variable [DecidableEq ι] [DecidableEq κ]

/-- Apply a generator to its source exchange matrix to compute the target. -/
def target (g : Generator ι) (B : SkewExchangeMatrix ι) : SkewExchangeMatrix ι :=
  match g with
  | .mutate k => B.mutate k
  | .permute σ => B.reindex σ.symm
  | .invert => -B

@[simp] theorem target_mutate (B : SkewExchangeMatrix ι) (k : ι) :
    (mutate k).target B = B.mutate k :=
  (rfl)

@[simp] theorem target_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    (permute σ).target B = B.reindex σ.symm :=
  (rfl)

@[simp] theorem target_invert (B : SkewExchangeMatrix ι) : invert.target B = -B :=
  (rfl)

/-- Applying a generator to the negated matrix negates its target as well. -/
@[simp]
theorem target_neg (g : Generator ι) (B : SkewExchangeMatrix ι) :
    g.target (-B) = -(g.target B) := by
  cases g <;> simp

@[simp]
theorem reverse_target_target (g : Generator ι) (B : SkewExchangeMatrix ι) :
    g.reverse.target (g.target B) = B := by
  cases g with
  | mutate | invert => simp
  | permute σ =>
    rw [reverse_permute, target_permute, target_permute, Equiv.symm_symm,
      SkewExchangeMatrix.reindex_trans, Equiv.symm_trans_self, SkewExchangeMatrix.reindex_refl]

@[simp]
theorem target_reindex (g : Generator ι) (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (g.reindex e).target (B.reindex e) = (g.target B).reindex e := by
  cases g with
  | mutate | invert => simp
  | permute σ =>
    apply SkewExchangeMatrix.ext
    ext i j
    simp

end Generator

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

/-- A signed cluster edge is a generator with its source and target exchange matrices.
The target is determined by the source and the generator. -/
@[ext]
structure Step (B C : SkewExchangeMatrix ι) where
  /-- The elementary operation performed by the edge. -/
  generator : Generator ι
  /-- The given target is the result of the elementary operation. -/
  target_eq : generator.target B = C

instance : Quiver (SkewExchangeMatrix ι) where
  Hom := Step

/-- A signed cluster word is a finite path of elementary operations between exchange matrices. -/
abbrev Word (B C : SkewExchangeMatrix ι) := Path B C

namespace Generator

/-- Make the edge prescribed by a generator at a given source. -/
def toStep (g : Generator ι) (B : SkewExchangeMatrix ι) : B ⟶ g.target B :=
  ⟨g, rfl⟩

@[simp]
theorem toStep_generator (g : Generator ι) (B : SkewExchangeMatrix ι) :
    Step.generator (g.toStep B) = g :=
  (rfl)

end Generator

/-- Reverse signed cluster edges by reversing their elementary operations. -/
instance : HasInvolutiveReverse (SkewExchangeMatrix ι) where
  reverse' s :=
    ⟨s.generator.reverse,
      (congrArg s.generator.reverse.target s.target_eq.symm).trans
        (s.generator.reverse_target_target _)⟩
  inv' s := by
    apply Step.ext
    exact s.generator.reverse_reverse

namespace Step

/-- Changing a step's endpoints by equality preserves its generator. -/
@[simp]
theorem generator_cast {B C B' C' : SkewExchangeMatrix ι} (s : B ⟶ C)
    (hB : B = B') (hC : C = C') :
    Step.generator (s.cast hB hC) = Step.generator s := by
  subst B' C'
  rfl

@[simp]
theorem reverse_generator {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    Step.generator (Quiver.reverse s) = s.generator.reverse :=
  (rfl)

variable {B C : SkewExchangeMatrix ι}

/-- Apply the same generator between the negated exchange matrices. -/
def neg (s : Step B C) : Step (-B) (-C) :=
  ⟨s.generator, by rw [Generator.target_neg, s.target_eq]⟩

@[simp]
theorem neg_generator (s : Step B C) : s.neg.generator = s.generator :=
  (rfl)

end Step

namespace SkewExchangeMatrix

/-- A morphism of signed cluster quivers is determined by its action on vertices and generators. -/
private theorem prefunctor_ext {F G : SkewExchangeMatrix ι ⥤q SkewExchangeMatrix κ}
    (h_obj : ∀ B, F.obj B = G.obj B)
    (h_gen : ∀ (B C : SkewExchangeMatrix ι) (s : B ⟶ C),
      Step.generator (F.map s) = Step.generator (G.map s)) : F = G := by
  apply Prefunctor.ext h_obj
  intro B C s
  apply Step.ext
  refine (h_gen B C s).trans ?_
  -- Transport changes the endpoint indices of an edge and leaves its generator intact.
  suffices ∀ {B B' C C' : SkewExchangeMatrix κ} (s : Step B C) (hB : B = B') (hC : C = C'),
      s.generator = (Eq.recOn hC (Eq.recOn hB s : Step B' C) : Step B' C').generator from
    this _ _ _
  intro B B' C C' s hB hC
  subst hB hC
  rfl

/-- Relabeling gives a quiver morphism, and its path map transports words to the new label type. -/
def reindexPrefunctor (e : ι ≃ κ) : SkewExchangeMatrix ι ⥤q SkewExchangeMatrix κ where
  obj B := B.reindex e
  map s := ⟨s.generator.reindex e, by rw [Generator.target_reindex, s.target_eq]⟩

@[simp]
theorem reindexPrefunctor_obj (e : ι ≃ κ) (B : SkewExchangeMatrix ι) :
    (reindexPrefunctor e).obj B = B.reindex e :=
  (rfl)

@[simp]
theorem reindexPrefunctor_map_generator (e : ι ≃ κ) {B C : SkewExchangeMatrix ι}
    (s : Step B C) : Step.generator ((reindexPrefunctor e).map s) = s.generator.reindex e :=
  (rfl)

instance (e : ι ≃ κ) : (reindexPrefunctor e).MapReverse where
  map_reverse' s := by
    apply Step.ext
    simp

@[simp]
theorem reindexPrefunctor_refl :
    reindexPrefunctor (Equiv.refl ι) = Prefunctor.id (SkewExchangeMatrix ι) := by
  apply prefunctor_ext
  · simp
  · simp

@[simp]
theorem reindexPrefunctor_comp (e : ι ≃ κ) (f : κ ≃ ρ) :
    reindexPrefunctor e ⋙q reindexPrefunctor f = reindexPrefunctor (e.trans f) := by
  apply prefunctor_ext
  · simp
  · simp

/-- Changing labels on a word commutes with reversing the sequence of operations. -/
@[simp]
theorem reindexPrefunctor_mapPath_reverse (e : ι ≃ κ) {B C : SkewExchangeMatrix ι}
    (w : Word B C) :
    (reindexPrefunctor e).mapPath w.reverse = ((reindexPrefunctor e).mapPath w).reverse := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end SkewExchangeMatrix

end QPainleve.Cluster

namespace Quiver.Path

open QPainleve.Cluster

variable {ι : Type*} [DecidableEq ι] {B C D : SkewExchangeMatrix ι}

/-- Count the global inversions in a signed cluster word. -/
def inversionCount : ∀ {C : SkewExchangeMatrix ι}, Word B C → ℕ :=
  addWeight (fun s ↦ (Step.generator s).inversionCount)

@[simp]
theorem inversionCount_nil : (Path.nil : Word B B).inversionCount = 0 :=
  addWeight_nil _ B

@[simp]
theorem inversionCount_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).inversionCount = w.inversionCount + (Step.generator s).inversionCount :=
  addWeight_cons _ w s

@[simp]
theorem inversionCount_toPath (s : B ⟶ C) :
    s.toPath.inversionCount = (Step.generator s).inversionCount := by
  simp [Hom.toPath]

/-- Concatenating words adds their inversion counts. -/
@[simp]
theorem inversionCount_comp (w : Word B C) (v : Word C D) :
    (w.comp v).inversionCount = w.inversionCount + v.inversionCount :=
  addWeight_comp _ w v

/-- Reversal preserves the number of global inversions. -/
@[simp]
theorem inversionCount_reverse (w : Word B C) :
    w.reverse.inversionCount = w.inversionCount := by
  induction w with
  | nil => simp [Path.reverse]
  | cons _ _ ih => simp [Path.reverse, ih, add_comm]

/-- Changing the labels of a signed word preserves its inversion count. -/
@[simp]
theorem inversionCount_reindex {κ : Type*} [DecidableEq κ] (e : ι ≃ κ) (w : Word B C) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).inversionCount = w.inversionCount := by
  induction w with
  | nil => simp
  | cons _ _ ih => simp [ih]

end Quiver.Path
