/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.SurfaceIntersection
public import QPainleve.AlgebraicGeometry.LineBundle.EffectiveClass
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.LinearAlgebra.BilinearForm.Isometry

import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Cremona isometries of a surface

Cremona isometries are the Picard isometries preserving both the canonical class
and the effective-class monoid, as in [Sakai, §4 (Cr1)–(Cr3)][Sakai].

[Sakai]: https://doi.org/10.1007/s002200100446
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] [Infinite k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "Pic" => Additive (LineBundleClass X)
local notation "B" => intersectionBilinForm k X
local notation "K" => Additive.ofMul (LineBundleClass.mk (QPainleve.canonicalBundle k X 2))

/-- The subgroup of Picard isometries fixing the canonical class and preserving
the effective classes in both directions. -/
def cremonaIsometryGroup : Subgroup (B).isometryGroup :=
  MulAction.stabilizer _ K ⊓ MulAction.stabilizer _ (X.effectiveClasses : Set Pic)

/-- Membership in the Cremona isometry group tests preservation of the canonical class
and the image of the effective-class monoid. -/
theorem mem_cremonaIsometryGroup_iff {g : (B).isometryGroup} :
    g ∈ cremonaIsometryGroup k X ↔
      g.val K = K ∧ X.effectiveClasses.map g.val.toAddMonoidHom = X.effectiveClasses := by
  rw [cremonaIsometryGroup, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  refine and_congr Iff.rfl ?_
  have hmap : (X.effectiveClasses.map g.val.toAddMonoidHom : Set Pic) =
      g • (X.effectiveClasses : Set Pic) := rfl
  rw [← hmap]
  exact SetLike.coe_set_eq

end TauCeti.AlgebraicGeometry.Chow
