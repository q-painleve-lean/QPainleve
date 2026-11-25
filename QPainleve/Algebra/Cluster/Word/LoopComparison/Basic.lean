/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.LinearAlgebra.Matrix.Kernel

/-!
# Integer comparison of typed signed loops

The comparison uses the computed exchange-kernel basis and a supplied boundary order table.
It can be used with typed paths obtained from generator lists or from a toric presentation.
-/

public section

namespace QPainleve.Cluster.SkewExchangeMatrix

variable {r n : ℕ} [NeZero n] (B : SkewExchangeMatrix (Fin r))

/-- Compare two loops by inversion sign, transported integral kernel columns, and forward
boundary label. The kernel basis is computed from `B`, and row zero supplies the initial
boundary orders. -/
def compareSignedLoops (orders : Fin n → Fin r → ℤ) (w v : Word B B) : Bool :=
  let basisVectors := B.matrix.intKernelBasisVectors.2
  decide (w.signedLoopInvariants basisVectors orders (orders 0) =
    v.signedLoopInvariants basisVectors orders (orders 0))

/-- The comparison returns true exactly when the three signed loop invariants agree. -/
@[simp]
theorem compareSignedLoops_eq_true_iff (orders : Fin n → Fin r → ℤ) (w v : Word B B) :
    B.compareSignedLoops orders w v = true ↔
      w.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0) =
        v.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0) := by
  simp [compareSignedLoops]

end QPainleve.Cluster.SkewExchangeMatrix
