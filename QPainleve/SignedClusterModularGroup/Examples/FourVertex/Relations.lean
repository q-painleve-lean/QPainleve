/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.LoopComparison.List
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.SignedClusterModularGroup.Examples.FourVertex.MarkedAction

/-!
# Deciding relations for the four-vertex seed

For the doubled-square seed of Bershtein, Gavrylenko and Marshakov,
*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1,
the inversion sign, two Casimir exponent columns, and the forward octagon label
decide equality of independent X pullbacks. The proof uses
`markedPicardEquiv` and `picardInvariants_injective`.
`Quiver.Path.xPullback_eq_iff_signedLoopInvariants_eq_of_charZero` extends the
criterion to every coefficient field, including when the exchange entries vanish
after reduction in that field.
-/

open CategoryTheory MulOpposite Quiver QPainleve.Cluster

namespace QPainleve.FourVertex

local notation "B" => exchangeMatrix
local notation "invariants[" w "]" =>
  Quiver.Path.signedLoopInvariants w
    (fun j ↦ (exchangeKernelEquiv (Pi.single j 1) : Fin 4 → ℤ))
    boundaryOrders (boundaryOrders 0)

private theorem exchangeMatrix_ne_zero : exchangeMatrix.matrix ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h 0) 1
  rw [exchangeMatrix_matrix_apply, Matrix.zero_apply] at hentry
  norm_num [chargeVector_eq, boundaryRay_eq, Matrix.det_fin_two_of] at hentry

private theorem xPullback_eq_iff_invariants_eq_complex (w v : Word B B) :
    w.xPullback ℂ = v.xPullback ℂ ↔ invariants[w] = invariants[v] := by
  have hcompare (u : Word B B) :
      picardInvariants (markedPicardEquiv (op (signedClusterModularGroupMap ℂ B (End.of u)))) =
        invariants[u] := by
    simpa only [exchangeKernelBasis_apply] using picardInvariants_markedPicardEquiv_loop u
  rw [← hcompare w, ← hcompare v, picardInvariants_injective.eq_iff,
    markedPicardEquiv.injective.eq_iff, op_injective.eq_iff, signedClusterModularGroupMap_eq_iff]
  rfl

public section

/-- For signed loops of the doubled-square seed, equality of the independent X
pullbacks is equivalent to equality of the sign, transported Casimir basis
vectors, and forward octagon label computed from component zero. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq (k : Type*) [Field k]
    (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔ invariants[w] = invariants[v] :=
  w.xPullback_eq_iff_signedLoopInvariants_eq_of_charZero v k ℂ
    exchangeMatrix_ne_zero (fun j ↦ exchangeKernelEquiv (Pi.single j 1)) boundaryOrders
    (boundaryOrders 0) (xPullback_eq_iff_invariants_eq_complex w v).mpr

/-- Decide equality of four-vertex X pullbacks by comparing their integer invariants. -/
def decidableXPullbackEq (k : Type*) [Field k] (w v : Word B B) :
    Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (invariants[w] = invariants[v])
    (xPullback_eq_iff_signedLoopInvariants_eq k w v).symm

/-- The integer comparator on four-vertex generator lists returns a Boolean exactly for two
closed words. The Boolean detects equality of their independent X pullbacks over any field. -/
theorem compareSignedLoopLists_eq_some_iff_xPullback_eq (k : Type*) [Field k]
    (gs hs : List (Generator (Fin 4))) (result : Bool) :
    (B).compareSignedLoopLists boundaryOrders gs hs = some result ↔
      ∃ w v : Word B B, w.generators = gs ∧ v.generators = hs ∧
        (result = true ↔ w.xPullback k = v.xPullback k) := by
  refine (B).compareSignedLoopLists_eq_some_iff_xPullback_eq k boundaryOrders ?_ gs hs result
  intro w v
  refine (B).compareSignedLoops_eq_true_iff_xPullback_eq k boundaryOrders w v fun β ↦ ?_
  simp only [xPullback_eq_iff_signedLoopInvariants_eq k, ← exchangeKernelBasis_apply,
    Path.signedLoopInvariants_eq_iff]

end

end QPainleve.FourVertex
