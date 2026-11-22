/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.Algebra.Cluster.XMutation.SubtractionFree
public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Data.Option.NAry
import Mathlib.Data.List.Induction

/-!
# Mutation-only segments of signed cluster words

A segment consisting entirely of mutations has a list of directions in execution order.
Its target matrix is given by Tau Ceti's `ExchangeMatrix.mutationWord`, and its X pullback
agrees with the list-based pullback over every field. In characteristic zero this identifies
the pullback on subtraction-free expressions with substitution by `YSeed.mutationWord`.
-/

public section

open QPainleve.Cluster TauCeti

namespace Quiver.Path

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {A B C : SkewExchangeMatrix ι}

/-- Read the mutation directions in execution order. A relabeling or global inversion anywhere
in the path gives `none`. -/
def mutationDirections : ∀ {B : SkewExchangeMatrix ι}, Word A B → Option (List ι)
  | _, .nil => some []
  | _, .cons w s =>
    match Step.generator s with
    | .mutate p => w.mutationDirections.map (· ++ [p])
    | .permute _ | .invert => none

@[simp]
theorem mutationDirections_nil : (Path.nil : Word A A).mutationDirections = some [] :=
  (rfl)

@[simp]
theorem mutationDirections_cons (w : Word A B) (s : B ⟶ C) :
    (w.cons s).mutationDirections = match Step.generator s with
      | .mutate p => w.mutationDirections.map (· ++ [p])
      | .permute _ | .invert => none :=
  (rfl)

/-- A path extended by one step has mutation directions exactly when the prefix does and
the last step is a mutation. -/
theorem mutationDirections_cons_eq_some_iff (w : Word A B) (s : B ⟶ C) (directions : List ι) :
    (w.cons s).mutationDirections = some directions ↔
      ∃ u p, w.mutationDirections = some u ∧ s.generator = .mutate p ∧
        u ++ [p] = directions := by
  cases hs : Step.generator s <;> simp [hs, Option.map_eq_some_iff]

@[simp]
theorem mutationDirections_toPath (s : A ⟶ B) :
    s.toPath.mutationDirections = match Step.generator s with
      | .mutate p => some [p]
      | .permute _ | .invert => none := by
  simp [Hom.toPath]

/-- Transport along endpoint equalities leaves the direction list unchanged. -/
@[simp]
theorem mutationDirections_cast {A' B' : SkewExchangeMatrix ι} (w : Word A B)
    (hA : A = A') (hB : B = B') : (w.cast hA hB).mutationDirections = w.mutationDirections := by
  subst hA hB
  rfl

/-- A concatenation has mutation directions when both segments do, in execution order. -/
@[simp]
theorem mutationDirections_comp (w : Word A B) (v : Word B C) :
    (w.comp v).mutationDirections = Option.map₂ List.append w.mutationDirections
      v.mutationDirections := by
  induction v with
  | nil => simp
  | cons v s ih =>
    cases hs : Step.generator s <;>
      simp [hs, ih, Option.map_map₂, Option.map₂_map_right, List.append_assoc]

/-- Reversing a mutation-only path reverses its list of directions. -/
@[simp]
theorem mutationDirections_reverse (w : Word A B) :
    w.reverse.mutationDirections = w.mutationDirections.map List.reverse := by
  induction w with
  | nil => rfl
  | cons w s ih =>
    cases hs : Step.generator s <;> simp [Path.reverse, hs, ih, Function.comp_def]

/-- Relabeling a mutation-only path relabels each direction. -/
@[simp]
theorem mutationDirections_reindex (e : ι ≃ κ) (w : Word A B) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).mutationDirections =
      w.mutationDirections.map (List.map e) := by
  induction w with
  | nil => rfl
  | cons w s ih =>
    cases hs : Step.generator s <;> simp [hs, ih, Function.comp_def]

/-- The target of a mutation-only path carries the native matrix obtained by mutating along
its directions. -/
theorem mutationWord_eq_of_mutationDirections (w : Word A B) {directions : List ι}
    (h : w.mutationDirections = some directions) : A.val.mutationWord directions = B.val := by
  induction w generalizing directions with
  | nil =>
    obtain rfl : [] = directions := by simpa using h
    simp
  | cons w s ih =>
    obtain ⟨u, p, hm, hs, rfl⟩ := (mutationDirections_cons_eq_some_iff w s directions).mp h
    have ht := s.target_eq
    rw [hs, Generator.target_mutate] at ht
    simp [ih hm, ← ht]

/-- The typed X pullback along a mutation-only path is the native list-based pullback.
This comparison works over every field. -/
theorem xPullback_eq_xMutationWord (w : Word A B) {directions : List ι}
    (h : w.mutationDirections = some directions) (k : Type*) [Field k] :
    w.xPullback k = xMutationWord k A.val directions := by
  induction w generalizing directions with
  | nil =>
    obtain rfl : [] = directions := by simpa using h
    simp [AlgEquiv.aut_one]
  | cons w s ih =>
    obtain ⟨u, p, hm, hs, rfl⟩ := (mutationDirections_cons_eq_some_iff w s directions).mp h
    ext x
    simp [ih hm, hs, xMutationWord_append, w.mutationWord_eq_of_mutationDirections hm,
      Step.xPullback_eq, SkewExchangeMatrix.val_matrix_apply_swap]

end Quiver.Path

namespace QPainleve.Cluster.SkewExchangeMatrix

open Quiver

variable {ι : Type*} [DecidableEq ι]

/-- Turn a native list of directions into a typed path with the native mutated matrix as
its target. -/
def mutationPath (B : SkewExchangeMatrix ι) (directions : List ι) :
    Word B ⟨B.val.mutationWord directions,
      (B.val.mutationWord_symmetrizer directions).trans B.property⟩ :=
  directions.reverseRecOn (Path.nil.cast rfl (Subtype.ext (B.val.mutationWord_nil.symm)))
    fun _ p w => (w.cons ((Generator.mutate p).toStep _)).cast rfl (Subtype.ext (by simp))

@[simp]
theorem mutationPath_nil (B : SkewExchangeMatrix ι) :
    B.mutationPath [] = Path.nil.cast rfl (Subtype.ext (B.val.mutationWord_nil.symm)) := by
  simp [mutationPath]

@[simp]
theorem mutationPath_append_singleton (B : SkewExchangeMatrix ι) (w : List ι) (p : ι) :
    B.mutationPath (w ++ [p]) =
      ((B.mutationPath w).cons ((Generator.mutate p).toStep _)).cast rfl
        (Subtype.ext (by simp)) := by
  simp [mutationPath]

/-- The typed path constructed from a list has precisely those mutation directions. -/
@[simp]
theorem mutationDirections_mutationPath (B : SkewExchangeMatrix ι) (w : List ι) :
    (B.mutationPath w).mutationDirections = some w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w p ih => simp [ih]

end QPainleve.Cluster.SkewExchangeMatrix

namespace Quiver.Path

variable {ι : Type*} [DecidableEq ι] {A B : SkewExchangeMatrix ι}

/-- A mutation-only path is recovered from its directions at the original source. -/
theorem mutationPath_cast_eq_of_mutationDirections (w : Word A B) {directions : List ι}
    (h : w.mutationDirections = some directions) :
    (A.mutationPath directions).cast rfl
      (Subtype.ext (w.mutationWord_eq_of_mutationDirections h)) = w := by
  induction w generalizing directions with
  | nil =>
    obtain rfl : [] = directions := by simpa using h
    simp
  | @cons B C w s ih =>
    obtain ⟨u, p, hm, hs, rfl⟩ := (mutationDirections_cons_eq_some_iff w s directions).mp h
    rcases s with ⟨g, rfl⟩
    obtain rfl : g = .mutate p := hs
    have hB : (⟨A.val.mutationWord u,
        (A.val.mutationWord_symmetrizer u).trans A.property⟩ : SkewExchangeMatrix ι) = B :=
      Subtype.ext (w.mutationWord_eq_of_mutationDirections hm)
    subst B
    have hw : A.mutationPath u = w := by simpa using ih hm
    simp only [SkewExchangeMatrix.mutationPath_append_singleton, cast_cast, cast_rfl_rfl, hw,
      cons.injEq, heq_eq_eq, true_and]
    exact Step.ext (Generator.toStep_generator _ _)

end Quiver.Path

noncomputable section

namespace Quiver.Path

variable {ι : Type*} [DecidableEq ι] {A B : SkewExchangeMatrix ι}
variable (k : Type*) [Field k] [CharZero k]

local notation "XField" => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

/-- On a mutation-only segment, pullback of every subtraction-free expression agrees with
substitution by the final native Y-seed coefficients. -/
theorem xPullback_comp_toXField (w : Word A B) {directions : List ι}
    (h : w.mutationDirections = some directions) :
    (w.xPullback k : XField →+* XField).comp (QsfZero.toXField k) =
      (QsfZero.toXField k).comp (QsfZero.eval
        (((⟨Qsf.X, A.val⟩ : YSeed ι (Qsf ι)).mutationWord directions).coefficient)) := by
  rw [w.xPullback_eq_xMutationWord h k, xMutationWord_comp_toXField]

end Quiver.Path
