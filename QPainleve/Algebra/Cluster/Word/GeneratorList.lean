/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Basic

/-!
# Generator lists and typed cluster words

A list of signed generators determines a typed path from any fixed source
exchange matrix. The intermediate and terminal matrices are computed in
execution order. Checking the terminal matrix gives a partial conversion
from generator lists to cluster loops.
-/

public section

open Quiver QPainleve.Cluster

namespace Quiver.Path

variable {ι : Type*} [DecidableEq ι] {B C : SkewExchangeMatrix ι}

private def reverseGenerators : {C : SkewExchangeMatrix ι} → Word B C → List (Generator ι)
  | _, .nil => []
  | _, .cons w s => s.generator :: reverseGenerators w

/-- The generators of a signed word in execution order. -/
def generators (w : Word B C) : List (Generator ι) :=
  (reverseGenerators w).reverse

@[simp]
theorem generators_nil : (Path.nil : Word B B).generators = [] :=
  (rfl)

@[simp]
theorem generators_cons {D : SkewExchangeMatrix ι} (w : Word B C) (s : C ⟶ D) :
    (w.cons s).generators = w.generators ++ [s.generator] := by
  simp [generators, reverseGenerators, List.reverse_cons]

@[simp]
theorem generators_cast {B' C' : SkewExchangeMatrix ι} (w : Word B C)
    (hB : B = B') (hC : C = C') : (w.cast hB hC).generators = w.generators := by
  subst B' C'
  rfl

@[simp]
theorem generators_comp {D : SkewExchangeMatrix ι} (w : Word B C) (v : Word C D) :
    (w.comp v).generators = w.generators ++ v.generators := by
  induction v with
  | nil => simp
  | cons v s ih => simp [ih, List.append_assoc]

end Quiver.Path

namespace QPainleve.Cluster.Generator

variable {ι : Type*} [DecidableEq ι] (B : SkewExchangeMatrix ι)

private def appendStep (w : Σ C, Word B C) (g : Generator ι) : Σ C, Word B C :=
  ⟨g.target w.1, w.2.cons (g.toStep w.1)⟩

/-- Interpret a list in execution order, returning its endpoint and its typed word. -/
def wordOfList (gs : List (Generator ι)) : Σ C, Word B C :=
  gs.foldl (appendStep B) ⟨B, .nil⟩

@[simp]
theorem wordOfList_nil : wordOfList B [] = ⟨B, .nil⟩ :=
  (rfl)

theorem wordOfList_append_singleton (gs : List (Generator ι)) (g : Generator ι) :
    wordOfList B (gs ++ [g]) =
      ⟨g.target (wordOfList B gs).1, (wordOfList B gs).2.cons (g.toStep (wordOfList B gs).1)⟩ := by
  rw [wordOfList, List.foldl_append]
  rfl

@[simp]
theorem generators_wordOfList (gs : List (Generator ι)) :
    (wordOfList B gs).2.generators = gs := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wordOfList_append_singleton]
    dsimp only
    rw [Path.generators_cons, toStep_generator, ih]

@[simp]
theorem wordOfList_generators {C : SkewExchangeMatrix ι} (w : Word B C) :
    wordOfList B w.generators = ⟨C, w⟩ := by
  induction w with
  | nil => simp
  | @cons A C w s ih =>
    rw [Path.generators_cons, wordOfList_append_singleton, ih]
    obtain ⟨g, rfl⟩ := s
    have he : g.toStep A = (⟨g, rfl⟩ : Step A (g.target A)) :=
      Step.ext (toStep_generator g A)
    dsimp only
    rw [he]

variable [Fintype ι]

private def toLoop? (w : Σ C, Word B C) : Option (Word B B) :=
  if h : w.1.matrix = B.matrix then
    some (w.2.cast rfl (SkewExchangeMatrix.ext h))
  else
    none

/-- Interpret a list as a loop if its terminal exchange matrix equals its source. -/
def loopOfList? (gs : List (Generator ι)) : Option (Word B B) :=
  toLoop? B (wordOfList B gs)

@[simp]
theorem loopOfList?_generators (w : Word B B) :
    loopOfList? B w.generators = some w := by
  unfold loopOfList?
  rw [wordOfList_generators]
  simp [toLoop?]

/-- The loop conversion returns exactly the typed loop with the given generator list. -/
@[simp]
theorem loopOfList?_eq_some_iff {gs : List (Generator ι)} {w : Word B B} :
    loopOfList? B gs = some w ↔ w.generators = gs := by
  refine ⟨?_, fun h ↦ h ▸ loopOfList?_generators B w⟩
  simp only [loopOfList?, toLoop?]
  split
  · rintro ⟨rfl⟩
    simp
  · simp

/-- A failed loop conversion means the computed endpoint differs from the source. -/
@[simp]
theorem loopOfList?_eq_none_iff {gs : List (Generator ι)} :
    loopOfList? B gs = none ↔ (wordOfList B gs).1 ≠ B := by
  simp only [loopOfList?, toLoop?]
  split
  · rename_i h
    simp [SkewExchangeMatrix.ext h]
  · rename_i h
    exact iff_of_true rfl (fun he ↦ h (congrArg SkewExchangeMatrix.matrix he))

end QPainleve.Cluster.Generator
