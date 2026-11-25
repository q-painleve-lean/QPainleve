/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Words

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.SignedClusterModularGroup.Examples.FourVertex.MarkedAction

/-!
# Deciding relations for the four-vertex seed

For the doubled-square seed of Bershtein, Gavrylenko and Marshakov,
*Cluster integrable systems, q-Painlevé equations and their quantization*, §3.1,
the inversion sign, two Casimir exponent columns, and the forward octagon label
decide equality of independent X pullbacks. The proof uses
`markedPicardEquiv` and `picardInvariants_injective`.
Subtraction-free evaluation extends the criterion to every characteristic-zero field.
-/

open CategoryTheory MulOpposite Quiver QPainleve.Cluster

namespace QPainleve.FourVertex

local notation "B" => exchangeMatrix
local notation "invariants[" w "]" =>
  Quiver.Path.signedLoopInvariants w
    (fun j ↦ (exchangeKernelEquiv (Pi.single j 1) : Fin 4 → ℤ))
    boundaryOrders (boundaryOrders 0)

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
theorem xPullback_eq_iff_signedLoopInvariants_eq (k : Type*) [Field k] [CharZero k]
    (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔ invariants[w] = invariants[v] :=
  (Path.xPullback_eq_iff_ySeed_coefficient_eq k w v).trans
    ((Path.xPullback_eq_iff_ySeed_coefficient_eq ℂ w v).symm.trans
      (xPullback_eq_iff_invariants_eq_complex w v))

/-- Decide equality of four-vertex X pullbacks by comparing their integer invariants. -/
def decidableXPullbackEq (k : Type*) [Field k] [CharZero k] (w v : Word B B) :
    Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (invariants[w] = invariants[v])
    (xPullback_eq_iff_signedLoopInvariants_eq k w v).symm

end

end QPainleve.FourVertex
