/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Topology.KrullDimension.Basic

/-!
# Closed points from a Krull dimension bound

A point whose codimension reaches a finite upper bound on the dimension of a `T₀` space is
closed. This is the topological form of `Order.isMin_of_le_coheight_of_krullDimLE`.
-/

public section

open Order TopologicalSpace

namespace QPainleve

attribute [local instance] specializationOrder

/-- A point whose codimension reaches the dimension bound has a closed singleton. -/
theorem isClosed_singleton_of_le_coheight_of_topologicalKrullDim_le {X : Type*}
    [TopologicalSpace X] [T0Space X] {n : ℕ}
    (hX : topologicalKrullDim X ≤ n) {x : X} (hx : n ≤ coheight x) :
    IsClosed ({x} : Set X) := by
  have : Order.KrullDimLE n X := by
    rw [Order.krullDimLE_iff, krullDim_eq_iSup_coheight]
    exact iSup_le fun y ↦ (TauCeti.coheight_le_topologicalKrullDim y).trans hX
  have hmin := isMin_of_le_coheight_of_krullDimLE hx
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  exact Set.mem_singleton_iff.mpr (hyx.antisymm (hmin hyx))

end QPainleve
