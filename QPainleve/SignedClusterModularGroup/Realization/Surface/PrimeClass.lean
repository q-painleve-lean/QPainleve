/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Surface.Boundary

/-!
# Picard classes of a packaged numbered boundary

The reference marking identifies the marked boundary classes with the classes
of the original numbered prime divisors.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.MarkedSurface

universe u

variable {K : Type u} [Field K] [IsSepClosed K] [Infinite K]

local notation "S" => Spec (CommRingCat.of K)

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [IsIntegral X]
  [X.IsProjectiveOver K] [SmoothOfRelativeDimension 2 (X ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

/-- The boundary class obtained by packaging a numbered Cartier divisor is the inverse
marking of the class of the original numbered prime divisor. -/
theorem boundaryClass_ofBoundary (D : X.IdealSheafData) [PrestableFamily (D.subscheme ↘ S)]
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm K X))
    (f : X ⤏ Y) (hD : D.IsEffectiveCartier) (j : ZMod n) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let M := ofBoundary D A μ f
    M.boundaryClass M.isEffectiveCartier_boundaryIdeal j =
      μ.symm (Additive.ofMul (LineBundleClass.primeDivisorClass
        (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)))) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let M := ofBoundary D A μ f
  -- Both primes are the image of the same numbered component's generic point.
  have hp : M.boundaryPrime M.isEffectiveCartier_boundaryIdeal j =
      D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j) := by
    apply Subtype.ext
    rw [M.coe_boundaryPrime, coe_boundaryPrimeEmbedding,
      NodalCycleNumbering.boundaryPrimeEquiv_apply_val]
    rfl
  apply μ.injective
  simp only [LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, μ.apply_symm_apply]
  rw [← ofBoundary_picardMarking D A μ f, M.picardMarking_boundaryClass, hp]
  rfl

end QPainleve.SignedClusterModularGroup.MarkedSurface
