/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Finite closed loci in Noetherian spaces

A closed locus consisting entirely of closed points in a quasi-sober Noetherian space is finite.
-/

public section

open TopologicalSpace

/-- A closed subset of a quasi-sober Noetherian space that consists of closed points is finite. -/
theorem IsClosed.finite_of_subset_closedPoints {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [NoetherianSpace X] {S : Set X} (hS : IsClosed S) (h : S ⊆ closedPoints X) : S.Finite := by
  obtain ⟨C, hC, hClosed, hIrreducible, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  rw [hcover]
  refine hC.sUnion fun V hV ↦ ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hIrreducible V hV) (hClosed V hV)
  have hxS : x ∈ S := hcover ▸ Set.mem_sUnion_of_mem hx.mem hV
  rw [← hx, (h hxS).closure_eq]
  exact Set.finite_singleton _
