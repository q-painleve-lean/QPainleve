/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.LoopComparison.List

/-!
# Relabeling the integer loop comparison

Changing the enumeration used for the matrix calculation can change the computed
integral basis. Equality of the two transport matrices is independent of that basis.
Relabeling also preserves the endpoint test, inversion parity, and the first
matching row of the boundary order table.
-/

public section

open Quiver

namespace QPainleve.Cluster.SkewExchangeMatrix

variable {r s n : ℕ} [NeZero n] (B : SkewExchangeMatrix (Fin r))

local notation "P[" e "]" => reindexPrefunctor e

/-- Relabeling both typed loops and the entries of the order table preserves the
Boolean comparison, including when the table has repeated rows. -/
theorem compareSignedLoops_reindex (e : Fin r ≃ Fin s)
    (orders : Fin n → Fin r → ℤ) (w v : Word B B) :
    (P[e].obj B).compareSignedLoops (fun j ↦ orders j ∘ e.symm)
        (P[e].mapPath w) (P[e].mapPath v) =
      B.compareSignedLoops orders w v := by
  apply Bool.eq_iff_iff.mpr
  simp only [compareSignedLoops_eq_true_iff_actions,
    Path.inversionCount_reindex, Path.tropicalBoundaryLabel_reindex,
    Path.exchangeKernelEquiv_reindex_eq_iff]

/-- The generator-list comparison commutes with changing the labels of the seed,
order table and both lists. Its failure to close a word is also preserved. -/
theorem compareSignedLoopLists_reindex (e : Fin r ≃ Fin s)
    (orders : Fin n → Fin r → ℤ) (gs hs : List (Generator (Fin r))) :
    (P[e].obj B).compareSignedLoopLists (fun j ↦ orders j ∘ e.symm)
        (gs.map (Generator.reindex e)) (hs.map (Generator.reindex e)) =
      B.compareSignedLoopLists orders gs hs := by
  simp only [compareSignedLoopLists_def, Generator.loopOfList?_reindex]
  cases Generator.loopOfList? B gs <;> cases Generator.loopOfList? B hs <;>
    simp [Option.map₂, compareSignedLoops_reindex]

variable {ι : Type*}

/-- The integer comparison on a finite label type can be run with any explicit
enumeration of the labels. The result is independent of that enumeration. -/
theorem compareSignedLoopLists_eq_of_enumeration (E : SkewExchangeMatrix ι)
    (e : ι ≃ Fin r) (f : ι ≃ Fin s) (orders : Fin n → ι → ℤ) (gs hs : List (Generator ι)) :
    (E.reindex e).compareSignedLoopLists (fun j ↦ orders j ∘ e.symm)
        (gs.map (Generator.reindex e)) (hs.map (Generator.reindex e)) =
      (E.reindex f).compareSignedLoopLists (fun j ↦ orders j ∘ f.symm)
        (gs.map (Generator.reindex f)) (hs.map (Generator.reindex f)) := by
  have hef : e.trans (e.symm.trans f) = f := by simp [← Equiv.trans_assoc]
  simpa only [reindexPrefunctor_obj, reindex_trans, List.map_map,
    Function.comp_def, Generator.reindex_trans, hef,
    Equiv.symm_trans, Equiv.trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply] using
    (compareSignedLoopLists_reindex (E.reindex e) (e.symm.trans f)
      (fun j ↦ orders j ∘ e.symm) (gs.map (Generator.reindex e))
      (hs.map (Generator.reindex e))).symm

end QPainleve.Cluster.SkewExchangeMatrix
