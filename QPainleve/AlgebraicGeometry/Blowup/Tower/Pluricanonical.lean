/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Point
import QPainleve.AlgebraicGeometry.Blowup.Tower.Canonical
import QPainleve.AlgebraicGeometry.Blowup.Tower.GlobalSections

/-!
# Pluricanonical sections under point blowups

Canonical powers have nonnegative total-transform exceptional coefficients, so the
global-sections comparison for those coefficients also identifies the pluricanonical
spaces on two smooth surfaces with a common resolution.

The bicanonical case gives the space used in [Vakil, *Complex Algebraic Surfaces*, Class 16][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass16A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {X Y Z : Scheme.{u}} {n d : ℕ} {T : BlowupTower X n Z}
  (k : Type u) [Field k] [PerfectField k] [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

variable [Z.Over (Spec (.of k))]

/-- A tower of closed point blowups of a smooth surface preserves each pluricanonical
space. The comparison applies to towers with infinitely near centers. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv
    [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
    (hT : IsClosedPointTower X T) [T.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Z 2).tensorPow m).obj 0) := by
  apply hT.nonempty_cohomologyZeroLinearEquiv_picardHom k _ (fun _ ↦ (m : ℤ))
    (fun _ ↦ Int.natCast_nonneg m)
  simp only [LineBundleClass.mk_tensorPow, hT.mk_canonicalBundle_picardHom k]
  rw [← toMul_nsmul, ← map_nsmul, Prod.smul_mk, ← ofMul_pow]
  simp only [Pi.smul_def, nsmul_eq_mul, mul_one]

variable [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {U : BlowupTower Y d Z}

/-- Two smooth surfaces with a common resolution by closed point blowups have isomorphic
spaces of global sections of every nonnegative tensor power of their canonical bundles. -/
theorem nonempty_cohomologyZero_pluricanonicalLinearEquiv_of_common_resolution
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Y U)
    [T.toBase.IsOver (Spec (.of k))] [U.toBase.IsOver (Spec (.of k))] (m : ℕ) :
    Nonempty (Cohomology ((canonicalBundle k X 2).tensorPow m).obj 0 ≃ₗ[k]
      Cohomology ((canonicalBundle k Y 2).tensorPow m).obj 0) := by
  have : SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k)) := by
    rw [← comp_over T.toBase (Spec (.of k))]
    exact hT.smoothOfRelativeDimension (X ↘ Spec (.of k))
  obtain ⟨eT⟩ := hT.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  obtain ⟨eU⟩ := hU.nonempty_cohomologyZero_pluricanonicalLinearEquiv k m
  exact ⟨eT.trans eU.symm⟩

end QPainleve.BlowupTower.IsClosedPointTower
