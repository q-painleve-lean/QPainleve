/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.GeneratorList
public import QPainleve.Algebra.Cluster.Word.Seed

/-!
# Moving relabelings to the end of a cluster word

A list of signed cluster generators acts on Y-seeds by a list of mutations and
inversions followed by a single relabeling. The relabeling sends final labels
to source labels, so moving it past a mutation transports the mutation direction
by that permutation.
-/

public section

open Quiver TauCeti QPainleve.Cluster

variable {ι P : Type*}

namespace Quiver.Path

variable [DecidableEq ι] [CoefficientSemifield P]

/-- Evaluating a typed word on a seed agrees with applying its generator list in execution order. -/
theorem ySeed_eq_foldl_generators {B C : SkewExchangeMatrix ι} (w : Word B C) (s : YSeed ι P) :
    w.ySeed s = w.generators.foldl (fun t g ↦ g.ySeed t) s := by
  induction w with
  | nil => simp
  | cons w e ih => simp [ih, List.foldl_append]

end Quiver.Path

namespace QPainleve.Cluster.Generator

variable [DecidableEq ι] [CoefficientSemifield P]

/-- A list of generators acts on a seed as mutations and inversions followed by one relabeling. -/
theorem exists_foldl_ySeed_eq_reindex (gs : List (Generator ι)) (s : YSeed ι P) :
    ∃ (ps : List (Option ι)) (τ : Equiv.Perm ι),
      gs.foldl (fun t g ↦ g.ySeed t) s =
        YSeed.reindex τ.symm
          ((ps.map mutationOrInversion).foldl (fun t g ↦ g.ySeed t) s) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], Equiv.refl ι, by simp⟩
  | append_singleton gs g ih =>
    obtain ⟨ps, τ, h⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, h]
    cases g with
    | mutate p =>
      refine ⟨ps ++ [some (τ p)], τ, ?_⟩
      simpa [List.foldl_append] using
        (ySeed_reindex (.mutate (τ p)) τ.symm
          ((ps.map mutationOrInversion).foldl (fun t g ↦ g.ySeed t) s))
    | invert =>
      exact ⟨ps ++ [none], τ, by simp [List.foldl_append]⟩
    | permute σ =>
      exact ⟨ps, σ.trans τ, by simp [Equiv.symm_trans, YSeed.reindex_reindex]⟩

end QPainleve.Cluster.Generator
