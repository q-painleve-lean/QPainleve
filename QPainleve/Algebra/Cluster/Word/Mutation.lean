/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.GeneratorList
public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.Algebra.Cluster.XMutation.SubtractionFree
public import Mathlib.Data.Option.NAry

/-!
# Mutation-only segments of signed cluster words

A segment consisting entirely of mutations has a list of directions in execution order.
The typed path is constructed by `Generator.wordOfList`, the same interpreter used for
lists that also contain permutations and inversions.
Its target matrix is given by Tau Ceti's `ExchangeMatrix.mutationWord`, and its X pullback
agrees with the list-based pullback over every field. In characteristic zero this identifies
the pullback on subtraction-free expressions with substitution by `YSeed.mutationWord`.
-/

public section

open QPainleve.Cluster TauCeti

namespace Quiver.Path

variable {ι κ : Type*}

private def mutationDirection? : Generator ι → Option ι
  | .mutate p => some p
  | .permute _ | .invert => none

private theorem mapM_mutationDirection_eq_some_iff (gs : List (Generator ι)) (directions : List ι) :
    gs.mapM mutationDirection? = some directions ↔ gs = directions.map Generator.mutate := by
  induction gs generalizing directions with
  | nil => cases directions <;> simp
  | cons g gs ih =>
    cases g <;> cases directions <;>
      simp [List.mapM_cons, mutationDirection?, Option.bind_eq_some_iff, ih, and_comm]

variable [DecidableEq ι] [DecidableEq κ] {A B C : SkewExchangeMatrix ι}

/-- Read the mutation directions in execution order. A relabeling or global inversion anywhere
in the path gives `none`. -/
def mutationDirections (w : Word A B) : Option (List ι) :=
  w.generators.mapM mutationDirection?

/-- A word has the given mutation directions exactly when its generators are those mutations
in execution order. -/
@[simp]
theorem mutationDirections_eq_some_iff (w : Word A B) (directions : List ι) :
    w.mutationDirections = some directions ↔ w.generators = directions.map Generator.mutate :=
  mapM_mutationDirection_eq_some_iff _ _

@[simp]
theorem mutationDirections_nil : (Path.nil : Word A A).mutationDirections = some [] :=
  (mutationDirections_eq_some_iff _ _).mpr generators_nil

@[simp]
theorem mutationDirections_toPath (s : A ⟶ B) :
    s.toPath.mutationDirections = match Step.generator s with
      | .mutate p => some [p]
      | .permute _ | .invert => none := by
  cases hs : Step.generator s <;>
    simp [mutationDirections, Hom.toPath, List.mapM_cons, mutationDirection?, hs]

/-- A concatenation has mutation directions when both segments do, in execution order. -/
@[simp]
theorem mutationDirections_comp (w : Word A B) (v : Word B C) :
    (w.comp v).mutationDirections = Option.map₂ List.append w.mutationDirections
      v.mutationDirections := by
  simp only [mutationDirections, generators_comp, List.mapM_append, Option.map₂,
    Option.map_eq_bind, Function.comp_def, Option.bind_eq_bind, Option.pure_def]
  rfl

@[simp]
theorem mutationDirections_cons (w : Word A B) (s : B ⟶ C) :
    (w.cons s).mutationDirections = match Step.generator s with
      | .mutate p => w.mutationDirections.map (· ++ [p])
      | .permute _ | .invert => none := by
  rw [← comp_toPath_eq_cons, mutationDirections_comp, mutationDirections_toPath]
  cases Step.generator s <;> simp

/-- A path extended by one step has mutation directions exactly when the prefix does and
the last step is a mutation. -/
theorem mutationDirections_cons_eq_some_iff (w : Word A B) (s : B ⟶ C) (directions : List ι) :
    (w.cons s).mutationDirections = some directions ↔
      ∃ u p, w.mutationDirections = some u ∧ s.generator = .mutate p ∧
        u ++ [p] = directions := by
  cases hs : Step.generator s <;> simp [hs, Option.map_eq_some_iff]

/-- Transport along endpoint equalities leaves the direction list unchanged. -/
@[simp]
theorem mutationDirections_cast {A' B' : SkewExchangeMatrix ι} (w : Word A B)
    (hA : A = A') (hB : B = B') : (w.cast hA hB).mutationDirections = w.mutationDirections := by
  simp [mutationDirections]

/-- Reversing a mutation-only path reverses its list of directions. -/
@[simp]
theorem mutationDirections_reverse (w : Word A B) :
    w.reverse.mutationDirections = w.mutationDirections.map List.reverse := by
  induction w with
  | nil => simp
  | cons w s ih =>
    cases hs : Step.generator s <;> simp [Path.reverse, hs, ih, Function.comp_def]

/-- Relabeling a mutation-only path relabels each direction. -/
@[simp]
theorem mutationDirections_reindex (e : ι ≃ κ) (w : Word A B) :
    ((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).mutationDirections =
      w.mutationDirections.map (List.map e) := by
  induction w with
  | nil => simp
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
  let w := Generator.wordOfList B (directions.map Generator.mutate)
  have hdirs : w.2.mutationDirections = some directions :=
    (w.2.mutationDirections_eq_some_iff _).mpr (Generator.generators_wordOfList B _)
  w.2.cast rfl (Subtype.ext (w.2.mutationWord_eq_of_mutationDirections hdirs).symm)

/-- The generators of the typed mutation path are the given mutations in execution order. -/
@[simp]
theorem generators_mutationPath (B : SkewExchangeMatrix ι) (directions : List ι) :
    (B.mutationPath directions).generators = directions.map Generator.mutate := by
  simp [mutationPath]

@[simp]
theorem mutationPath_nil (B : SkewExchangeMatrix ι) :
    B.mutationPath [] = Path.nil.cast rfl (Subtype.ext (B.val.mutationWord_nil.symm)) := by
  apply Path.generators_injective
  simp

@[simp]
theorem mutationPath_append_singleton (B : SkewExchangeMatrix ι) (w : List ι) (p : ι) :
    B.mutationPath (w ++ [p]) =
      ((B.mutationPath w).cons ((Generator.mutate p).toStep _)).cast rfl
        (Subtype.ext (by simp)) := by
  apply Path.generators_injective
  simp

/-- The typed path constructed from a list has precisely those mutation directions. -/
@[simp]
theorem mutationDirections_mutationPath (B : SkewExchangeMatrix ι) (w : List ι) :
    (B.mutationPath w).mutationDirections = some w :=
  (Path.mutationDirections_eq_some_iff _ _).mpr (B.generators_mutationPath w)

end QPainleve.Cluster.SkewExchangeMatrix

namespace Quiver.Path

variable {ι : Type*} [DecidableEq ι] {A B : SkewExchangeMatrix ι}

/-- A mutation-only path is recovered from its directions at the original source. -/
theorem mutationPath_cast_eq_of_mutationDirections (w : Word A B) {directions : List ι}
    (h : w.mutationDirections = some directions) :
    (A.mutationPath directions).cast rfl
      (Subtype.ext (w.mutationWord_eq_of_mutationDirections h)) = w := by
  apply generators_injective
  simpa only [generators_cast, SkewExchangeMatrix.generators_mutationPath] using
    ((w.mutationDirections_eq_some_iff _).mp h).symm

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
