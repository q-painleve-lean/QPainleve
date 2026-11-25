/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Blowup.Tower.TotalTransform
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Multiplicity
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Recovering nodal boundary multiplicities from intersections

The positive kernel generator of the boundary intersection matrix recovers the
multiplicities of the total transform. The coefficient criterion in
`IsNodalBoundaryTower.mem_centre_iff_two_le_coeff_totalTransform` identifies the
weight-one components as the primes that survive the contraction.
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

/-- Compute the total boundary weights and identify the surviving prime divisors
of a nodal contraction from its numbered intersection matrix. A numbered prime
survives exactly when the corresponding computed weight is one. -/
theorem intKernelGenerator_eq_totalTransform_and_surviving
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s))
    (hconn : _root_.IsConnected (D.support : Set X))
    (hnef : IsNef k s (mk hD.toInvertibleSheaf)⁻¹)
    (hsq : Chow.classIntersectionNumber k X (mk hD.toInvertibleSheaf)⁻¹
      (mk hD.toInvertibleSheaf)⁻¹ = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType s
    letI := T.isNoetherian
    letI := hT.isClosedPointTower.isIntegral s
    letI : Y.Over S := ⟨T.toBase ≫ s⟩
    letI := (hT.isClosedPointTower.smoothOfRelativeDimension s)
    letI (y : Y) :=
      (T.toBase ≫ s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
    let htotal := hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD
    let W := htotal.toCartierDivisor.toWeilDivisor
    ∀ (e : Fin m ≃ W.support) (i : Fin m),
      (Chow.primeIntersectionMatrix k (Subtype.val ∘ e)).intKernelGenerator i =
          some (fun j ↦ W (e j)) ∧
        ∀ j, T.toBase ((e j).val : Y) ∈ D.boundaryPrimes ↔ W (e j) = 1 := by
  intro htotal W e i
  let : IsNoetherian X := isNoetherian_of_finiteType s
  let : IsNoetherian Y := T.isNoetherian
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral s
  let : Y.Over S := ⟨T.toBase ≫ s⟩
  let : SmoothOfRelativeDimension 2 (T.toBase ≫ s) :=
    hT.isClosedPointTower.smoothOfRelativeDimension s
  let (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (T.toBase ≫ s).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  let : IsNormalScheme Y := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  have : IsReduced D.subscheme := hnodal.isReduced
  refine ⟨hT.isClosedPointTower.intKernelGenerator_eq_totalTransform k hD hconn hnef hsq e i,
    fun j ↦ ?_⟩
  have hnonneg : 0 ≤ W :=
    (Scheme.CartierDivisor.isEffective_iff_toWeilDivisor_nonneg _).mp
      (hT.isClosedPointTower.isEffectiveCartier_totalTransform s hD).isEffective_toCartierDivisor
  have hpos : 0 < W (e j) :=
    (hnonneg (e j)).lt_of_ne (Finsupp.mem_support_iff.mp (e j).property).symm
  have hcontract : T.toBase ((e j).val : Y) ∈ T.toBase.centre ↔ 2 ≤ W (e j) :=
    hT.mem_centre_iff_two_le_coeff_totalTransform hD hnodal (e j).val
  let : Smooth s := SmoothOfRelativeDimension.smooth 2 s
  let : IsRegular X := IsRegular.of_smooth s
  let := hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two s
  have hmem : ((e j).val : Y) ∈ (D.comap T.toBase).support :=
    by_contra fun h ↦ (Finsupp.mem_support_iff.mp (e j).property)
      ((htotal.coeff_toWeilDivisor_eq_zero_iff _).mpr h)
  rw [D.mem_boundaryPrimes_iff_mem_isoLocus_of_mem_boundaryPrimes_comap _
    (mem_boundaryPrimes.mpr ⟨hmem, (e j).val.property⟩),
    ← SetLike.mem_coe, ← Set.notMem_compl_iff, ← Scheme.Hom.centre_def, hcontract]
  omega

end QPainleve.BlowupTower.IsNodalBoundaryTower
