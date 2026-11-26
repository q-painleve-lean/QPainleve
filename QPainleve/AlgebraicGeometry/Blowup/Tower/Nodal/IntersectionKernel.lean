/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.TotalTransform
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Multiplicity
import QPainleve.AlgebraicGeometry.CartierDivisor.BoundaryPrimes
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Recovering nodal boundary multiplicities from intersections

For a numbering of the boundary primes upstairs, the positive kernel generator
of their intersection matrix gives the total transform multiplicities. The
weight-one components are the primes that survive the contraction.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData LineBundleClass

universe u

namespace QPainleve.BlowupTower.IsNodalBoundaryTower

variable (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {n m : ℕ} {T : BlowupTower X n Y} {D : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)

/-- Recover the total boundary weights in the given numbering of the primes upstairs.
A prime survives the nodal contraction exactly when its computed weight is one. -/
theorem intKernelGenerator_eq_totalTransform_and_surviving
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnef : IsNef k s (mk hD.toInvertibleSheaf)⁻¹)
    (hsq : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0)
    (e : Fin m ≃ (D.comap T.toBase).boundaryPrimes) (i : Fin m) :
    letI : IsNoetherian X := isNoetherian_of_finiteType s
    letI := T.isNoetherian
    letI := hT.isClosedPointTower.isIntegral s
    letI : Y.Over S := ⟨T.toBase ≫ s⟩
    letI := (hT.isClosedPointTower.smoothOfRelativeDimension s)
    letI (y : Y) :=
      (T.toBase ≫ s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
    let htotal := hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD
    let W := htotal.toCartierDivisor.toWeilDivisor
    let E := D.comap T.toBase
    (Chow.primeIntersectionMatrix k (E.boundaryPrimeEmbedding ∘ e)).intKernelGenerator i =
        some (fun j ↦ W (E.boundaryPrimeEmbedding (e j))) ∧
      ∀ j, T.toBase (e j).val ∈ D.boundaryPrimes ↔ W (E.boundaryPrimeEmbedding (e j)) = 1 := by
  intro htotal W E
  let : IsNoetherian X := isNoetherian_of_finiteType s
  let : IsNoetherian Y := T.isNoetherian
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral s
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (T.toBase ≫ s) :=
    hT.isClosedPointTower.smoothOfRelativeDimension s
  let (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (T.toBase ≫ s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  have : IsReduced D.subscheme := hnodal.isReduced
  refine ⟨?_, fun j ↦ hT.toBase_mem_boundaryPrimes_iff_coeff_totalTransform_eq_one hD hnodal (e j)⟩
  simpa only [Function.comp_def, Equiv.trans_apply,
    IsEffectiveCartier.boundaryPrimesEquivWeilSupport_apply_val] using
    hT.isClosedPointTower.intKernelGenerator_eq_totalTransform k hD hconn hnef hsq
      (e.trans htotal.boundaryPrimesEquivWeilSupport) i

end QPainleve.BlowupTower.IsNodalBoundaryTower
