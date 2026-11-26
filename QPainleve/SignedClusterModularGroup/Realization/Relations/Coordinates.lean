/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Coordinates
public import QPainleve.SignedClusterModularGroup.Realization.Relations.RayOrders
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Reference
public import QPainleve.SignedClusterModularGroup.Realization.Relations.SurvivingOffsets

/-!
# Signed loop comparison from a toric ray table

The input lists primitive ray coordinates in cyclic order from boundary component
zero, together with the ray offset of every ordered center and the set of offsets
that survive a nodal contraction. The center offsets determine the exchange
matrix. The surviving offsets determine the determinant orders used in the
tropical boundary search. An integer kernel calculation supplies the Casimir
basis. The resulting certificate for the exchange matrix and order table can
be used with the typed and generator-list comparisons.
-/

public section

open AlgebraicGeometry CategoryTheory Module
open QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

namespace CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation i b r L γ)
  {c₀ : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyCoordinateRelationCones : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance instNeZeroCoordinateRelationLength : NeZero Q.length := Q.neZero
local instance instPrestableCoordinateRelationBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "raysFromOrigin" =>
  Q.fan.rayEquivOfNodalCycleNumbering Q.regular (Q.cycle.rotate Q.origin)
local notation "rayAt" => Q.fan.rayFinEquivOfNodalCycleNumbering Q.regular Q.cycle Q.origin
local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M

/-- The coordinates of the center and surviving rays certify the computed exchange matrix
and order table. The ray indices are cyclic offsets from the ray of component zero. -/
theorem isSignedLoopComparisonInput_of_rayCoordinates (p₀ : fiber[M₀,c₀])
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (survivors : Set.powersetCard (Fin Q.length) n)
    (hray : ∀ j, j ∈ survivors ∨ j ∈ Set.range centerRay →
      ray j = b.repr (rayAt j).primitiveGenerator)
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j)
    (hsurvivors : survivors = p₀.survivingBoundaryRayOffsets cartier[M₀]) :
    Q.IsSignedLoopComparisonInput p₀ (SkewExchangeMatrix.ofChargeCoordinates (ray ∘ centerRay))
      (boundaryOrderTable (ray ∘ centerRay) ray survivors) := by
  have hcharge (j : Fin r) : (ray ∘ centerRay) j = b.repr (Q.rays j).primitiveGenerator := by
    rw [Function.comp_apply, hray _ (Or.inr (Set.mem_range_self j)), hcenter j]
  refine ⟨?_, p₀.boundaryOrderTable_eq (Φ := Q.fan) cartier[M₀] survivors hsurvivors
    (ray ∘ centerRay) ray hcharge (fun j hj ↦ hray j (Or.inl hj))⟩
  simpa only [Fan.rayChargeMap_single, funext hcharge] using
    SkewExchangeMatrix.ofChargeCoordinates_matrix_eq_chargeExchangeMatrix b
      (Fan.rayChargeMap Q.rays)

/-- The integer coefficients of a pulled-back ample class determine the surviving ray
offsets. With the center and surviving ray coordinates, they certify the exchange matrix
and the computed order table for the signed loop checker. -/
theorem isSignedLoopComparisonInput_of_polarization
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    {H : LineBundleClass M₀.surface} (hH : H.IsAmple)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (selfIntersection toricCoeff : ZMod Q.length → ℤ) (exceptionalCoeff : Fin r → ℤ)
    (hself : ∀ j, selfIntersection j = Q.fan.rayBoundarySelfIntersection Q.regular
      (raysFromOrigin j))
    (hcoords : (Q.fan.rayDivisorToPicard Q.regular (toricCoeff ∘ (raysFromOrigin).symm),
        exceptionalCoeff) = Q.inclusion (M₀.picardMarking.symm (Additive.ofMul H)))
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j) :
    let survivors := p₀.survivingRayOffsetsOfPolarization hnodal₀ Q.complete hH
      selfIntersection toricCoeff centerRay exceptionalCoeff hself hcenter hcoords
    (∀ j, j ∈ survivors ∨ j ∈ Set.range centerRay →
      ray j = b.repr (rayAt j).primitiveGenerator) →
    Q.IsSignedLoopComparisonInput p₀ (SkewExchangeMatrix.ofChargeCoordinates (ray ∘ centerRay))
      (boundaryOrderTable (ray ∘ centerRay) ray survivors) := by
  intro survivors hray
  exact Q.isSignedLoopComparisonInput_of_rayCoordinates p₀ ray centerRay survivors hray hcenter
    (p₀.survivingRayOffsetsOfPolarization_eq hnodal₀ Q.complete hH
      selfIntersection toricCoeff centerRay exceptionalCoeff hself hcenter hcoords)

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
