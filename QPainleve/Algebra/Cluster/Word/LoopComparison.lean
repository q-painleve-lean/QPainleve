/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.GeneratorList
public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.LinearAlgebra.Matrix.Kernel

import Mathlib.Data.Option.NAry

/-!
# Integer comparison of signed generator lists

Starting from an exchange matrix, validate the computed endpoints and compare
the signed loop invariants against the supplied boundary order table. A
comparison of two valid loops returns a Boolean. The geometric relation
criterion supplies the interpretation of this Boolean as equality of pullbacks.
-/

public section

open Quiver

namespace QPainleve.Cluster.SkewExchangeMatrix

variable {r n : ℕ} [NeZero n] (B : SkewExchangeMatrix (Fin r))

/-- Compare the integer invariants of two generator lists based at `B`, using the
computed kernel basis and the first row of the supplied boundary orders as the starting
vector. Return `none` if either list fails to return to `B`. -/
def compareSignedLoopLists (orders : Fin n → Fin r → ℤ)
    (gs hs : List (Generator (Fin r))) : Option Bool :=
  Option.map₂
    (fun w v ↦
      let basisVectors := B.matrix.intKernelBasisVectors.2
      decide (w.signedLoopInvariants basisVectors orders (orders 0) =
        v.signedLoopInvariants basisVectors orders (orders 0)))
    (Generator.loopOfList? B gs) (Generator.loopOfList? B hs)

/-- The comparison fails exactly when at least one computed endpoint differs from `B`. -/
@[simp]
theorem compareSignedLoopLists_eq_none_iff (orders : Fin n → Fin r → ℤ)
    (gs hs : List (Generator (Fin r))) :
    B.compareSignedLoopLists orders gs hs = none ↔
      (Generator.wordOfList B gs).1 ≠ B ∨ (Generator.wordOfList B hs).1 ≠ B := by
  simp [compareSignedLoopLists, Option.map₂_eq_none_iff]

/-- A Boolean result certifies that both lists give loops. Its truth value is
the equality of the signed integer invariants of those loops. -/
theorem compareSignedLoopLists_eq_some_iff (orders : Fin n → Fin r → ℤ)
    (gs hs : List (Generator (Fin r))) (result : Bool) :
    B.compareSignedLoopLists orders gs hs = some result ↔
      ∃ w v : Word B B, w.generators = gs ∧ v.generators = hs ∧
        (result = true ↔
          w.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0) =
            v.signedLoopInvariants B.matrix.intKernelBasisVectors.2 orders (orders 0)) := by
  cases result <;> simp [compareSignedLoopLists, Option.mem_def]

end QPainleve.Cluster.SkewExchangeMatrix
