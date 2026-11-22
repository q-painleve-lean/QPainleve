/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.Tactic.LinearCombination

/-!
# Signed cluster words

The vertices are skew-symmetric integer exchange matrices. An edge records a mutation, a
permutation of the labels, or simultaneous sign reversal. Mathlib's quiver paths then retain
the source and target of a word, including under concatenation, reversal, and changes of labels.
Two generators with the same endpoints still record distinct operations.

The vertices use Tau Ceti's `ExchangeMatrix` with unit symmetrizer. Its entries are
the negatives of the geometric exchange entries used in the cluster `X` formulas.
Mutation and relabeling use `ExchangeMatrix.mutation` and `ExchangeMatrix.reindex`.
For mutation and permutations see Fock and Goncharov, *Cluster ensembles, quantization and
the dilogarithm*, §1.2.2. For the operation adjoining sign reversal see Bershtein, Gavrylenko
and Marshakov, *Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1.
-/

public section

namespace QPainleve.Cluster

open scoped Int
open Quiver

variable {ι κ ρ : Type*}

/-- A square Tau Ceti exchange matrix with unit symmetrizer, stored in the convention
`B = -ε` for geometric exchange matrix `ε`. -/
structure SkewExchangeMatrix (ι : Type*) where
  /-- The native exchange matrix, whose pivot row gives the geometric pivot column. -/
  toExchangeMatrix : TauCeti.ExchangeMatrix (Function.Embedding.refl ι)
  /-- The unit symmetrizer witnesses skew-symmetry. -/
  toExchangeMatrix_symmetrizer : toExchangeMatrix.symmetrizer = fun _ ↦ 1

namespace SkewExchangeMatrix

attribute [simp] toExchangeMatrix_symmetrizer

/-- The geometric exchange matrix `ε` governing the cluster `X` formulas. -/
def matrix (B : SkewExchangeMatrix ι) : Matrix ι ι ℤ :=
  -B.toExchangeMatrix.matrix

/-- The native matrix is the negative of the geometric matrix. -/
theorem toExchangeMatrix_matrix (B : SkewExchangeMatrix ι) :
    B.toExchangeMatrix.matrix = -B.matrix := by
  simp [matrix]

/-- Construct a vertex from the exchange entries in the geometric convention. -/
def ofMatrix (ε : Matrix ι ι ℤ) (hε : ε.IsSkewSymmetrizer (fun _ ↦ 1)) :
    SkewExchangeMatrix ι :=
  ⟨⟨-ε, fun _ ↦ 1, hε.neg.submatrix (Function.Embedding.refl ι)⟩, rfl⟩

@[simp]
theorem matrix_ofMatrix (ε : Matrix ι ι ℤ) (hε : ε.IsSkewSymmetrizer (fun _ ↦ 1)) :
    (ofMatrix ε hε).matrix = ε := by
  simp [ofMatrix, matrix]

@[ext]
theorem ext {B C : SkewExchangeMatrix ι} (h : B.matrix = C.matrix) : B = C := by
  obtain ⟨B, hB⟩ := B
  obtain ⟨C, hC⟩ := C
  congr 1
  apply TauCeti.ExchangeMatrix.ext
  · exact neg_injective h
  · exact hB.trans hC.symm

/-- The geometric exchange matrix is skew-symmetrized by the unit vector. -/
theorem isSkewSymmetrizer (B : SkewExchangeMatrix ι) : B.matrix.IsSkewSymmetrizer (fun _ ↦ 1) := by
  simpa [matrix, Function.Embedding.coe_refl] using B.toExchangeMatrix.isSkewSymmetrizer.neg

@[simp]
theorem ofMatrix_matrix (B : SkewExchangeMatrix ι) : ofMatrix B.matrix B.isSkewSymmetrizer = B :=
  ext (matrix_ofMatrix _ _)

/-- Skew-symmetry interchanges the two entries with a sign change. -/
theorem apply_swap (B : SkewExchangeMatrix ι) (i j : ι) : B.matrix j i = -B.matrix i j := by
  simpa using B.isSkewSymmetrizer.mul_apply j i

/-- The native row entry used by coefficient mutation is the geometric column entry. -/
theorem toExchangeMatrix_matrix_apply (B : SkewExchangeMatrix ι) (i j : ι) :
    B.toExchangeMatrix.matrix i j = B.matrix j i := by
  simp [toExchangeMatrix_matrix, B.apply_swap i j]

@[simp]
theorem apply_diag (B : SkewExchangeMatrix ι) (i : ι) : B.matrix i i = 0 :=
  B.isSkewSymmetrizer.apply_self i

instance : Neg (SkewExchangeMatrix ι) where
  neg B :=
    ⟨{ B.toExchangeMatrix with
        matrix := -B.toExchangeMatrix.matrix
        isSkewSymmetrizer := B.toExchangeMatrix.isSkewSymmetrizer.neg },
      B.toExchangeMatrix_symmetrizer⟩

@[simp]
theorem neg_matrix (B : SkewExchangeMatrix ι) : (-B).matrix = -B.matrix :=
  (rfl)

@[simp]
theorem neg_neg (B : SkewExchangeMatrix ι) : -(-B) = B := by
  ext i j
  simp

/-- Transport a matrix to new labels using the same equivalence for rows and columns. -/
def reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) : SkewExchangeMatrix κ :=
  ⟨TauCeti.ExchangeMatrix.reindex e e (by simp) B.toExchangeMatrix, by simp [Function.comp_def]⟩

@[simp]
theorem toExchangeMatrix_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (B.reindex e).toExchangeMatrix =
      TauCeti.ExchangeMatrix.reindex e e (by simp) B.toExchangeMatrix :=
  (rfl)

@[simp]
theorem reindex_matrix (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (B.reindex e).matrix = B.matrix.submatrix e.symm e.symm := by
  simp [matrix, Matrix.submatrix_neg]

@[simp]
theorem reindex_refl (B : SkewExchangeMatrix ι) : B.reindex (Equiv.refl ι) = B := by
  ext i j
  simp

@[simp]
theorem reindex_trans (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (f : κ ≃ ρ) :
    (B.reindex e).reindex f = B.reindex (e.trans f) := by
  ext i j
  simp

@[simp]
theorem reindex_neg (B : SkewExchangeMatrix ι) (e : ι ≃ κ) :
    (-B).reindex e = -(B.reindex e) := by
  ext i j
  simp

variable [DecidableEq ι] [DecidableEq κ]

/-- Mutate the exchange matrix at label `k`. -/
def mutate (B : SkewExchangeMatrix ι) (k : ι) : SkewExchangeMatrix ι :=
  ⟨B.toExchangeMatrix.mutation k, by simp⟩

@[simp]
theorem toExchangeMatrix_mutate (B : SkewExchangeMatrix ι) (k : ι) :
    (B.mutate k).toExchangeMatrix = B.toExchangeMatrix.mutation k :=
  (rfl)

@[simp]
theorem mutate_matrix (B : SkewExchangeMatrix ι) (k : ι) :
    (B.mutate k).matrix = TauCeti.matrixMutation (Function.Embedding.refl ι) B.matrix k := by
  simp only [matrix, toExchangeMatrix_mutate, TauCeti.ExchangeMatrix.mutation_matrix,
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
  apply SkewExchangeMatrix.ext
  simp only [matrix, toExchangeMatrix_mutate, TauCeti.ExchangeMatrix.mutation_mutation]

@[simp]
theorem mutate_neg (B : SkewExchangeMatrix ι) (k : ι) : (-B).mutate k = -(B.mutate k) := by
  apply SkewExchangeMatrix.ext
  simp

@[simp]
theorem mutate_reindex (B : SkewExchangeMatrix ι) (e : ι ≃ κ) (k : ι) :
    (B.reindex e).mutate (e k) = (B.mutate k).reindex e := by
  apply SkewExchangeMatrix.ext
  simp only [matrix, toExchangeMatrix_mutate, toExchangeMatrix_reindex,
    TauCeti.ExchangeMatrix.mutation_reindex]

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

@[simp]
theorem reverse_generator {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    Step.generator (Quiver.reverse s) = s.generator.reverse :=
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
